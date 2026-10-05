/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateRootDuality

/-! # Original Galois compatibility of perfect root-valued Tate Cartier duality -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

/-- The original Galois action on each finite root group, before choosing any generator. -/
def tateRootLevelGaloisHom (σ : Field.absoluteGaloisGroup K) (n : ℕ) :
    TateRootLevel (AlgebraicClosure K) p n →+ TateRootLevel (AlgebraicClosure K) p n :=
  (show rootsOfUnity (p ^ n) (AlgebraicClosure K) →*
      rootsOfUnity (p ^ n) (AlgebraicClosure K) from
    { toFun x := ⟨σ • x.val, by
        rw [mem_rootsOfUnity, ← smul_pow', x.property, smul_one]⟩
      map_one' := by apply Subtype.ext; exact smul_one σ
      map_mul' := by intro x y; apply Subtype.ext; exact smul_mul' σ _ _ }).toAdditive

/-- Finite conjugation commutes with the actual p-adic residue scalars. -/
def tateRootLevelGalois (σ : Field.absoluteGaloisGroup K) (n : ℕ) :
    TateRootLevel (AlgebraicClosure K) p n →ₗ[ℤ_[p]] TateRootLevel (AlgebraicClosure K) p n where
  __ := tateRootLevelGaloisHom σ n
  map_smul' a x := ZMod.map_smul (tateRootLevelGaloisHom σ n) (PadicInt.toZModPow n a) x

/-- Original Galois conjugation preserves the whole coherent-root module. -/
def tateRootGalois (σ : Field.absoluteGaloisGroup K) :
    TateRootModule (AlgebraicClosure K) p →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p where
  toFun x := ⟨fun n ↦ tateRootLevelGalois σ n (x.val n), by
    intro m n h
    apply Additive.toMul.injective
    apply Subtype.ext
    have he := congrArg (fun z : TateRootLevel (AlgebraicClosure K) p m ↦ σ • z.toMul.val)
      (x.property h)
    change (σ • (x.val n).toMul.val) ^ (p ^ (n - m)) = σ • (x.val m).toMul.val
    rw [← smul_pow']
    exact he⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (tateRootLevelGalois σ n).map_add _ _
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact (tateRootLevelGalois σ n).map_smul a _

/-- Root conjugation has the original identity law. -/
theorem tateRootGalois_one (x : TateRootModule (AlgebraicClosure K) p) :
    tateRootGalois 1 x = x := by
  apply tateRoot_ext
  intro n
  exact congrArg Additive.ofMul (one_smul (Field.absoluteGaloisGroup K) (x.val n).toMul.val)

/-- Root conjugation has the original composition law. -/
theorem tateRootGalois_mul (σ τ : Field.absoluteGaloisGroup K)
    (x : TateRootModule (AlgebraicClosure K) p) :
    tateRootGalois (σ * τ) x = tateRootGalois σ (tateRootGalois τ x) := by
  apply tateRoot_ext
  intro n
  exact congrArg Additive.ofMul (mul_smul σ τ (x.val n).toMul.val)

namespace PDivisibleSystem
variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {height : ℕ} (X : PDivisibleSystem R K p height)

/-- Perfect Tate duality intertwines the two original actions and conjugation of genuine roots. -/
theorem tateRootDuality_galois (σ : Field.absoluteGaloisGroup K)
    (y : X.CartierTate) (x : X.tateSequences) :
    X.tateRootDuality (σ • y) (σ • x) = tateRootGalois σ (X.tateRootDuality y x) := by
  apply tateRoot_ext
  intro n
  exact congrArg Additive.ofMul (X.cartierTatePairing_smul σ y x n)
end PDivisibleSystem
end ThreeAdicPlan
