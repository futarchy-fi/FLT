/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import FLT.GroupScheme.IntegralEtaleModel

/-!
# Constant finite-flat objects over the integers with two inverted

The canonical integral étale model of a trivial finite Galois module realizes
the constant group scheme. In particular this constructs the constant group
of order three and the zero object with their full geometric point comparisons.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A finite abelian group with the trivial rational Galois action. -/
def constantPoints (A : Type) [AddCommGroup A] [Finite A] :
    FiniteContinuousGaloisModule := by
  let : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) A :=
    { smul := fun _ a ↦ a
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl
      smul_zero := fun _ ↦ rfl
      smul_add := fun _ _ _ ↦ rfl }
  exact { Carrier := A, continuous := ⟨fun x y ↦ by
    change IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | x = y}
    by_cases h : x = y <;> simp [h]⟩ }

/-- Constant points are fixed pointwise. -/
theorem constantPoints_smul (A : Type) [AddCommGroup A] [Finite A]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : constantPoints A) : σ • a = a := rfl

/-- The canonical finite étale model of a constant finite group over `ℤ[1/2]`. -/
def constantEtaleModel (A : Type) [AddCommGroup A] [Finite A] :
    FiniteEtaleModel ZInvTwo (constantPoints A) := by
  let : Fact (∀ p ∈ ({2} : Finset ℕ), p.Prime) := ⟨by simp [Nat.prime_two]⟩
  have hu : UnramifiedOutside {2} (constantPoints A) := ⟨fun _ _ _ _ _ _ ↦ rfl⟩
  let T (d : {n : ℤ // n ≠ 0}) :=
    @FiniteEtaleModel (Localization.Away d.val) _ ℚ _
      (IsLocalization.Away.lift d.val (show IsUnit (algebraMap ℤ ℚ d.val) by
        exact IsUnit.mk0 _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ ℚ)).mpr
          d.property))).toAlgebra (constantPoints A)
  change T ⟨2, by decide⟩
  have hd : (⟨∏ p ∈ ({2} : Finset ℕ), (p : ℤ), ZInvPrimes.denominator_ne_zero {2}⟩ :
      {n : ℤ // n ≠ 0}) = ⟨2, by decide⟩ := by
    apply Subtype.ext
    simp
  rw [← hd]
  exact (constantPoints A).integralEtaleModel {2} hu

/-- The constant finite-flat group associated with a finite abelian group. -/
def constantFiniteFlat (A : Type) [AddCommGroup A] [Finite A] : FiniteFlatObject ZInvTwo :=
  ⟨constantPoints A, (constantEtaleModel A).toHasFiniteFlatModel⟩

/-- The constant group scheme `ℤ/3ℤ` over `ℤ[1/2]`. -/
def constantThree : FiniteFlatObject ZInvTwo := constantFiniteFlat (ZMod 3)

/-- The zero finite-flat group scheme over `ℤ[1/2]`. -/
def zeroFiniteFlat : FiniteFlatObject ZInvTwo := constantFiniteFlat PUnit

end ThreeAdicPlan
