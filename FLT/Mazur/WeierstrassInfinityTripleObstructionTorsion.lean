/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleAffineLocalization
public import FLT.Mazur.WeierstrassInfinityTripleCoordinateIdeal

/-!
# A genuine annihilator of the full infinity associativity obstruction

One power of the five-coordinate denominator annihilates the entire residual
ideal, including both quadratic defect coefficients. This is a vanishing
relation from the four actual laws, rather than a new presentation of that
ideal. Removing the denominator torsion remains a separate obligation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

/-- Two power-torsion elements have a common annihilating power. -/
theorem infinity_common_power_annihilator {S : Type*} [CommRing S] (d x y : S)
    (hx : ∃ n : ℕ, d ^ n * x = 0) (hy : ∃ n : ℕ, d ^ n * y = 0) :
    ∃ n : ℕ, d ^ n * x = 0 ∧ d ^ n * y = 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_, ?_⟩
  · calc
      d ^ (a + b) * x = d ^ b * (d ^ a * x) := by rw [pow_add]; ring
      _ = 0 := by rw [ha, mul_zero]
  · rw [pow_add, mul_assoc, hb, mul_zero]

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The two normalized coordinate differences have one actual power annihilator. -/
theorem infinityTriple_coordinate_common_torsion :
    ∃ n : ℕ,
      infinityTripleAffineDenominator W hΔ ^ n *
        (infinityTripleScalarX W hΔ 6 - infinityTripleScalarX W hΔ 5) = 0 ∧
      infinityTripleAffineDenominator W hΔ ^ n *
        (infinityTripleScalarZ W hΔ 6 - infinityTripleScalarZ W hΔ 5) = 0 := by
  obtain ⟨n, hx, hz⟩ := infinity_common_power_annihilator _ _ _
    (infinityTriple_output_difference_torsion W hΔ (coord W 1 0))
    (infinityTriple_output_difference_torsion W hΔ (coord W 1 2))
  refine ⟨n, ?_, ?_⟩
  · change infinityTripleAffineDenominator W hΔ ^ n *
      (infinityTripleScalarPoint W hΔ 6 (coord W 1 0) -
        infinityTripleScalarPoint W hΔ 5 (coord W 1 0)) = 0
    linear_combination -hx
  · change infinityTripleAffineDenominator W hΔ ^ n *
      (infinityTripleScalarPoint W hΔ 6 (coord W 1 2) -
        infinityTripleScalarPoint W hΔ 5 (coord W 1 2)) = 0
    linear_combination -hz

/-- A single denominator power belongs to the annihilator of the exact residual ideal. -/
theorem infinityTriple_obstruction_annihilator :
    ∃ n : ℕ, infinityTripleAffineDenominator W hΔ ^ n ∈
      (Ideal.span ({infinityTripleNegLineResidual W hΔ 6 2,
        infinityTripleNegMinor W hΔ 5 6} : Set Γ(InfinityTripleFull W hΔ, ⊤))).annihilator := by
  obtain ⟨n, hx, hz⟩ := infinityTriple_coordinate_common_torsion W hΔ
  refine ⟨n, ?_⟩
  change infinityTripleAffineDenominator W hΔ ^ n ∈
    (Ideal.span ({infinityTripleNegLineResidual W hΔ 6 2,
      infinityTripleNegMinor W hΔ (infinityTripleOutputIndex 2) 6} :
        Set Γ(InfinityTripleFull W hΔ, ⊤))).annihilator
  rw [infinityTripleResidual_coordinate_span]
  apply (Submodule.mem_annihilator_span _ _).mpr
  rintro ⟨a, ha⟩
  rcases ha with rfl | ha
  · exact hx
  · rcases ha with rfl
    exact hz

/-- In particular the two requested residuals are killed by the same actual denominator power. -/
theorem infinityTriple_residual_common_torsion :
    ∃ n : ℕ,
      infinityTripleAffineDenominator W hΔ ^ n * infinityTripleNegLineResidual W hΔ 6 2 = 0 ∧
      infinityTripleAffineDenominator W hΔ ^ n * infinityTripleNegMinor W hΔ 5 6 = 0 := by
  obtain ⟨n, hn⟩ := infinityTriple_obstruction_annihilator W hΔ
  exact ⟨n, Submodule.mem_annihilator.mp hn _ (Ideal.subset_span (by simp)),
    Submodule.mem_annihilator.mp hn _ (Ideal.subset_span (by simp))⟩

/-- Regularity of this explicit denominator would remove the remaining infinity obstruction. -/
theorem infinityTripleFull_assoc_of_affineDenominator_regular
    (hd : IsRegular (infinityTripleAffineDenominator W hΔ)) :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
      infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ := by
  rw [infinityTripleFull_assoc_iff_line_residual]
  obtain ⟨n, he, hm⟩ := infinityTriple_residual_common_torsion W hΔ
  exact ⟨(hd.pow n).left (he.trans (mul_zero _).symm),
    (hd.pow n).left (hm.trans (mul_zero _).symm)⟩

end FLT.Mazur.WeierstrassIntegralChart
