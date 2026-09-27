/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionRoots
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Counting odd torsion from a separable division polynomial

The quadratic equation above an odd torsion x-coordinate is separable.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {k : Type*} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]

omit [E.IsElliptic] in
/-- Away from the two-division roots, the curve equation is separable in the
y-coordinate. -/
theorem separable_polynomial_of_Ψ₂Sq_ne_zero {x : k} (hd : E.Ψ₂Sq.eval x ≠ 0) :
    (E.toAffine.polynomial.map (evalRingHom x)).Separable := by
  let q := E.toAffine.polynomial.map (evalRingHom x)
  let d := E.Ψ₂Sq.eval x
  have hder : q.derivative = E.ψ₂.map (evalRingHom x) := by
    simp [q, Affine.polynomial, ψ₂, Affine.polynomialY, derivative_pow]
  have hid : C d = q.derivative ^ 2 - 4 * q := by
    have he := congrArg (Polynomial.map (evalRingHom x)) (E.C_Ψ₂Sq)
    simpa only [Polynomial.map_C, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_ofNat, ← hder, q, d, coe_evalRingHom] using he
  rw [Polynomial.separable_def']
  refine ⟨C d⁻¹ * (-4), C d⁻¹ * q.derivative, ?_⟩
  change C d⁻¹ * (-4) * q + C d⁻¹ * q.derivative * q.derivative = 1
  calc
    _ = C d⁻¹ * (q.derivative ^ 2 - 4 * q) := by ring
    _ = C d⁻¹ * C d := by rw [hid]
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hd, map_one]

omit [E.IsElliptic] in
/-- Away from the two-division roots, a separably closed field supplies
exactly two y-coordinates on the curve. -/
theorem card_equation_of_Ψ₂Sq_ne_zero [IsSepClosed k] {x : k}
    (hd : E.Ψ₂Sq.eval x ≠ 0) : Nat.card {y : k // E.toAffine.Equation x y} = 2 := by
  let q := E.toAffine.polynomial.map (evalRingHom x)
  have hs : q.Separable := E.separable_polynomial_of_Ψ₂Sq_ne_zero hd
  have he (y : k) : E.toAffine.Equation x y ↔ y ∈ q.rootSet k := by
    rw [Polynomial.mem_rootSet_of_ne hs.ne_zero]
    simp only [q, aeval_def, Algebra.algebraMap_self, eval₂_id, eval_map,
      eval₂_evalRingHom, Affine.Equation]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree hs (by
      simpa using IsSepClosed.splits_of_separable _ hs)]
  exact (Affine.monic_polynomial.natDegree_map (evalRingHom x)).trans
    Affine.natDegree_polynomial

/-- An odd division-polynomial root is not a two-division root. -/
theorem eval_Ψ₂Sq_ne_zero_of_isRoot_preΨ {n : ℕ} (hn : Odd n) {x : k}
    (hx : (E.preΨ n).IsRoot x) : E.Ψ₂Sq.eval x ≠ 0 := by
  have hc := Polynomial.aeval_ne_zero_of_isCoprime (E.isCoprime_preΨ_ΨSq_two hn) x
  have hx' : (E.preΨ n).eval x = 0 := hx
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, ΨSq_two, hx', ne_self_iff_false,
    false_or] using hc

/-- Specializing the curve equation at an odd division-polynomial root
gives a separable quadratic in the y-coordinate. -/
theorem separable_polynomial_over_preΨ_root {n : ℕ} (hn : Odd n) {x : k}
    (hx : (E.preΨ n).IsRoot x) :
    (E.toAffine.polynomial.map (evalRingHom x)).Separable :=
  E.separable_polynomial_of_Ψ₂Sq_ne_zero (E.eval_Ψ₂Sq_ne_zero_of_isRoot_preΨ hn hx)

/-- Above an odd division-polynomial root there are exactly two rational
y-coordinates over a separably closed field, including in characteristic two. -/
theorem card_equation_of_isRoot_preΨ [IsSepClosed k] {n : ℕ} (hn : Odd n) {x : k}
    (hx : (E.preΨ n).IsRoot x) : Nat.card {y : k // E.toAffine.Equation x y} = 2 :=
  E.card_equation_of_Ψ₂Sq_ne_zero (E.eval_Ψ₂Sq_ne_zero_of_isRoot_preΨ hn hx)

/-- Nonzero odd torsion points are the pairs of a division-polynomial root
and a y-coordinate satisfying the curve equation. -/
noncomputable def nonzeroOddTorsionEquivRootFibers [DecidableEq k] {n : ℕ}
    (hn : Odd n) (hp : E.preΨ n ≠ 0) :
    {P : E.toAffine.Point // n • P = 0 ∧ P ≠ 0} ≃
      (x : (E.preΨ n).rootSet k) × {y : k // E.toAffine.Equation x.val y} where
  toFun P := by
    obtain ⟨P, ht, hz⟩ := P
    cases P with
    | zero => exact (hz rfl).elim
    | some x y h =>
      refine ⟨⟨x, (Polynomial.mem_rootSet_of_ne hp).mpr ?_⟩, ⟨y, h.1⟩⟩
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, Polynomial.IsRoot] using
        (E.isRoot_preΨ_iff_nsmul_eq_zero h hn).mpr ht
  invFun P := by
    have h := E.toAffine.equation_iff_nonsingular.mp P.2.property
    refine ⟨Affine.Point.some P.1.val P.2.val h, ?_, Affine.Point.some_ne_zero h⟩
    apply (E.isRoot_preΨ_iff_nsmul_eq_zero h hn).mp
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, Polynomial.IsRoot] using
      (Polynomial.mem_rootSet_of_ne hp).mp P.1.property
  left_inv P := by
    obtain ⟨P, ht, hz⟩ := P
    cases P with
    | zero => exact (hz rfl).elim
    | some x y h => rfl
  right_inv P := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := P
    rfl

/-- Counting the two points above each odd division-polynomial root and the
identity gives the cardinality of odd torsion over a separably closed field. -/
theorem card_odd_torsion_eq_roots [DecidableEq k] [IsSepClosed k] {n : ℕ}
    (hn : Odd n) (hp : E.preΨ n ≠ 0) :
    Nat.card {P : E.toAffine.Point // n • P = 0} =
      1 + 2 * Nat.card ((E.preΨ n).rootSet k) := by
  classical
  let T := {P : E.toAffine.Point // n • P = 0}
  let z : T := ⟨0, by simp⟩
  let e : {P : T // P ≠ z} ≃ {P : E.toAffine.Point // n • P = 0 ∧ P ≠ 0} :=
    { toFun := fun P => ⟨P.val.val, P.val.property, fun h => P.property (Subtype.ext h)⟩
      invFun := fun P => ⟨⟨P.val, P.property.1⟩, fun h =>
        P.property.2 (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hroot (x : (E.preΨ n).rootSet k) : (E.preΨ n).IsRoot x.val := by
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, Polynomial.IsRoot] using
      (Polynomial.mem_rootSet_of_ne hp).mp x.property
  have hcard (x : (E.preΨ n).rootSet k) :
      Nat.card {y : k // E.toAffine.Equation x.val y} = 2 :=
    E.card_equation_of_isRoot_preΨ hn (hroot x)
  let (x : (E.preΨ n).rootSet k) : Finite {y : k // E.toAffine.Equation x.val y} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let er := e.trans (E.nonzeroOddTorsionEquivRootFibers hn hp)
  let : Finite {P : T // P ≠ z} := Finite.of_equiv _ er.symm
  change Nat.card T = _
  rw [← Nat.card_congr (Equiv.optionSubtypeNe z), Finite.card_option,
    Nat.card_congr er, Nat.card_sigma]
  simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]
  omega

/-- A separable odd division polynomial implies the expected torsion
cardinality over a separably closed field. -/
theorem card_odd_torsion_of_separable [DecidableEq k] [IsSepClosed k] {n : ℕ}
    (hn : Odd n) (hchar : (n : k) ≠ 0) (hsep : (E.preΨ n).Separable) :
    Nat.card {P : E.toAffine.Point // n • P = 0} = n ^ 2 := by
  rw [E.card_odd_torsion_eq_roots hn hsep.ne_zero, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree hsep (by
      simpa using IsSepClosed.splits_of_separable _ hsep)]
  have hc : ((n : ℤ) : k) ≠ 0 := by exact_mod_cast hchar
  have he : ¬Even (n : ℤ) := by
    simpa only [Int.even_coe_nat] using (Nat.not_even_iff_odd.mpr hn)
  rw [E.natDegree_preΨ hc, ite_eq_right he, Int.natAbs_natCast]
  have hm : n % 2 = 1 := Nat.odd_iff.mp hn
  have hs : n ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hm]
  omega

end WeierstrassCurve
