/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleInputRegular
public import FLT.Mazur.WeierstrassInfinityTripleObstructionTorsion

/-!
# Only the intermediate-sum denominator remains

Cancel the three original input coordinates using their proved regularity on
the actual full intersection. The exact residuals are power torsion for the
product of the two intermediate Z coordinates alone.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The product of the three original input Z coordinates. -/
def infinityTripleInputDenominator : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarZ W hΔ 0 * infinityTripleScalarZ W hΔ 1 *
    infinityTripleScalarZ W hΔ 2

/-- The remaining denominator uses just the two intermediate sums. -/
def infinityTripleIntermediateDenominator : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarZ W hΔ 3 * infinityTripleScalarZ W hΔ 4

/-- The original five-coordinate denominator splits into input and intermediate factors. -/
theorem infinityTripleAffineDenominator_factor :
    infinityTripleAffineDenominator W hΔ =
      infinityTripleInputDenominator W hΔ * infinityTripleIntermediateDenominator W hΔ := by
  simp only [infinityTripleAffineDenominator, Fin.prod_univ_succ, Fin.prod_univ_zero,
    mul_one, infinityTripleInputDenominator,
    infinityTripleIntermediateDenominator]
  change infinityTripleScalarZ W hΔ 0 * (infinityTripleScalarZ W hΔ 1 *
    (infinityTripleScalarZ W hΔ 2 * (infinityTripleScalarZ W hΔ 3 *
      infinityTripleScalarZ W hΔ 4))) = _
  ring

/-- The original input factor is regular on the actual full member. -/
theorem infinityTripleInputDenominator_regular :
    IsRegular (infinityTripleInputDenominator W hΔ) :=
  ((infinityTripleScalarZ_input_regular W hΔ 0).mul
    (infinityTripleScalarZ_input_regular W hΔ 1)).mul
    (infinityTripleScalarZ_input_regular W hΔ 2)

/-- Input powers can be removed from any actual five-coordinate torsion relation. -/
theorem infinityTriple_cancel_input_torsion (a : Γ(InfinityTripleFull W hΔ, ⊤)) (n : ℕ)
    (h : infinityTripleAffineDenominator W hΔ ^ n * a = 0) :
    infinityTripleIntermediateDenominator W hΔ ^ n * a = 0 := by
  apply ((infinityTripleInputDenominator_regular W hΔ).pow n).left
  dsimp only
  rw [mul_zero, ← mul_assoc, ← mul_pow, ← infinityTripleAffineDenominator_factor]
  exact h

/-- Every output difference is killed by a power of the two intermediate coordinates alone. -/
theorem infinityTriple_output_intermediate_torsion (a : Coordinate W 1) :
    ∃ n : ℕ, infinityTripleIntermediateDenominator W hΔ ^ n *
      (infinityTripleScalarPoint W hΔ 5 a - infinityTripleScalarPoint W hΔ 6 a) = 0 := by
  obtain ⟨n, hn⟩ := infinityTriple_output_difference_torsion W hΔ a
  exact ⟨n, infinityTriple_cancel_input_torsion W hΔ _ n hn⟩

/-- The exact two residuals have a common annihilating intermediate-coordinate power. -/
theorem infinityTriple_residual_intermediate_torsion :
    ∃ n : ℕ,
      infinityTripleIntermediateDenominator W hΔ ^ n *
        infinityTripleNegLineResidual W hΔ 6 2 = 0 ∧
      infinityTripleIntermediateDenominator W hΔ ^ n *
        infinityTripleNegMinor W hΔ 5 6 = 0 := by
  obtain ⟨n, he, hm⟩ := infinityTriple_residual_common_torsion W hΔ
  exact ⟨n, infinityTriple_cancel_input_torsion W hΔ _ n he,
    infinityTriple_cancel_input_torsion W hΔ _ n hm⟩

/-- Only regularity of the two intermediate sums is still needed for full infinity associativity. -/
theorem infinityTripleFull_assoc_of_intermediate_regular
    (h : IsRegular (infinityTripleIntermediateDenominator W hΔ)) :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
      infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ := by
  apply infinityTripleFull_assoc_of_affineDenominator_regular
  rw [infinityTripleAffineDenominator_factor]
  exact (infinityTripleInputDenominator_regular W hΔ).mul h

end FLT.Mazur.WeierstrassIntegralChart
