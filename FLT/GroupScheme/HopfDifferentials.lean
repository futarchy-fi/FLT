/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Differentials of a commutative group scheme killed by an integer

Square-zero extensions detect derivations. In the commutative convolution ring,
two algebra-valued points differing by a square-zero map and killed by `n`
have difference annihilated by `n`. Applying this to the universal derivation
proves the corresponding statement for Kähler differentials.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace HopfAlgebra

/-- The first-order binomial formula in a commutative ring. -/
theorem pow_add_of_sq_zero {T : Type*} [CommRing T] (g d : T) (hd : d ^ 2 = 0)
    (n : ℕ) : (g + d) ^ (n + 1) = g ^ (n + 1) + (n + 1) • (g ^ n * d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (g + d), ih]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [pow_succ g (n + 1), pow_succ g n]
    linear_combination ((n : T) + 1) * g ^ n * hd

/-- Two points of order dividing `n` with square-zero difference have `n`-torsion difference. -/
theorem nsmul_sub_eq_zero_of_pow_eq_one {T : Type*} [CommRing T] (f g : T) (n : ℕ)
    (hf : f ^ n = 1) (hg : g ^ n = 1) (hd : (f - g) ^ 2 = 0) : n • (f - g) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := pow_add_of_sq_zero g (f - g) hd n
    rw [add_sub_cancel, hf, hg] at h
    have hz : (n + 1) • (g ^ n * (f - g)) = 0 := by
      exact add_left_cancel (h.symm.trans (add_zero 1).symm)
    have hm := congrArg (g * ·) hz
    rw [mul_smul_comm, ← mul_assoc, ← pow_succ', hg, one_mul, mul_zero] at hm
    exact hm

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Bialgebra R A] [Algebra R B]

/-- Postcomposition preserves convolution powers of algebra maps. -/
theorem comp_convPow (f : A →ₐ[R] B) (g : A →ₐ[R] A) (n : ℕ) :
    f.comp (ofConv (toConv g ^ n)) = ofConv (toConv (f.comp g) ^ n) := by
  induction n with
  | zero => ext x; simp [AlgHom.convOne_def]
  | succ n ih =>
    rw [pow_succ, AlgHom.comp_convMul_distrib, ih, pow_succ]

/-- If multiplication by `n` is zero on a group scheme, every algebra-valued point
has convolution power `n` equal to the identity point. -/
theorem convPow_eq_one_of_id (n : ℕ)
    (hn : toConv (AlgHom.id R A) ^ n = (1 : WithConv (A →ₐ[R] A)))
    (f : A →ₐ[R] B) : toConv f ^ n = 1 := by
  apply ofConv_injective
  have h := comp_convPow f (AlgHom.id R A) n
  rw [hn, AlgHom.comp_id] at h
  rw [← h]
  ext x
  simp [AlgHom.convOne_def]

variable [Coalgebra.IsCocomm R A]
variable {N : Type*} [AddCommGroup N] [Module A N] [Module R N]
  [IsScalarTower R A N]

/-- The right action used for the square-zero extension is the given commutative action. -/
local instance derivationRightModule : Module Aᵐᵒᵖ N :=
  Module.compHom _ ((RingHom.id A).fromOpposite mul_comm)
/-- The left and right actions on the target of a derivation agree. -/
local instance derivationCentralScalar : IsCentralScalar A N := ⟨fun _ _ ↦ rfl⟩
/-- Restriction of scalars is compatible with the chosen right action. -/
local instance derivationRightScalarTower : IsScalarTower R Aᵐᵒᵖ N :=
  ⟨fun r a x ↦ smul_assoc r a.unop x⟩

/-- A derivation, viewed as the algebra map into the trivial square-zero extension. -/
def derivationPoint (d : Derivation R A N) : A →ₐ[R] TrivSqZeroExt A N where
  toFun a := ⟨a, d a⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · rfl
    · change d (a * b) = a • d b + b • d a
      exact d.leibniz a b
  map_zero' := by ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact d.map_add a b
  commutes' r := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact d.map_algebraMap r

/-- Multiplication by `n` on a commutative group scheme annihilates every derivation
when the group scheme itself is killed by `n`. -/
theorem nsmul_derivation_eq_zero (n : ℕ)
    (hn : toConv (AlgHom.id R A) ^ n = (1 : WithConv (A →ₐ[R] A)))
    (d : Derivation R A N) (a : A) : n • d a = 0 := by
  let f := derivationPoint d
  let g := TrivSqZeroExt.inlAlgHom R A N
  let F := toConv f.toLinearMap
  let G := toConv g.toLinearMap
  have hF : F ^ n = 1 := by
    rw [← AlgHom.toLinearMap_convPow, convPow_eq_one_of_id n hn, AlgHom.toLinearMap_convOne]
  have hG : G ^ n = 1 := by
    rw [← AlgHom.toLinearMap_convPow, convPow_eq_one_of_id n hn, AlgHom.toLinearMap_convOne]
  have hdiff (y : A) : (F - G).ofConv y = TrivSqZeroExt.inr (d y) := by
    apply TrivSqZeroExt.ext
    · change y - y = 0
      exact sub_self y
    · change d y - 0 = d y
      exact sub_zero _
  have hsq : (F - G) ^ 2 = 0 := by
    rw [pow_two]
    apply WithConv.ext
    apply LinearMap.ext
    intro x
    rw [(Coalgebra.Repr.arbitrary R x).convMul_apply]
    change ∑ i ∈ (Coalgebra.Repr.arbitrary R x).index,
      (F - G).ofConv ((Coalgebra.Repr.arbitrary R x).left i) *
      (F - G).ofConv ((Coalgebra.Repr.arbitrary R x).right i) = 0
    apply Finset.sum_eq_zero
    intro i hi
    rw [hdiff, hdiff]
    exact TrivSqZeroExt.inr_mul_inr A _ _
  have h := nsmul_sub_eq_zero_of_pow_eq_one F G n hF hG hsq
  have ha := congrArg (fun t : WithConv (A →ₗ[R] TrivSqZeroExt A N) => (t a).snd) h
  change ((n • (F - G)).ofConv a).snd = 0 at ha
  rw [ofConv_smul, LinearMap.smul_apply, TrivSqZeroExt.snd_smul] at ha
  change n • (d a - 0) = 0 at ha
  simpa only [sub_zero] using ha

/-- The Kähler differentials of a commutative group scheme killed by `n` are killed by `n`.
Finiteness and flatness are not needed for this algebraic statement. -/
theorem nsmul_kaehlerDifferential_eq_zero (n : ℕ)
    (hn : toConv (AlgHom.id R A) ^ n = (1 : WithConv (A →ₐ[R] A)))
    (ω : KaehlerDifferential R A) : n • ω = 0 := by
  have h : (n • LinearMap.id : KaehlerDifferential R A →ₗ[A] KaehlerDifferential R A) = 0 := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    exact nsmul_derivation_eq_zero n hn (KaehlerDifferential.D R A) a
  exact LinearMap.congr_fun h ω

end HopfAlgebra
