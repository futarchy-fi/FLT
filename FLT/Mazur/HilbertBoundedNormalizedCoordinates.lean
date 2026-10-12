/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedCoordinateRing

/-!
# Normalized bounded coordinates of monomial Hilbert charts

The selected monomial columns are the identity matrix. Quotienting by these
explicit normalization equations still maps onto the original Hilbert chart
ring, without modifying its full ring-law or basis-equation ideal.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)

/-- Cache the coefficient ring while normalizing the universal quotient. -/
local instance normalizedCoordinatesCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the selected monomial chart ring. -/
local instance normalizedCoordinatesChartRing :
    CommRing (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)) := inferInstance
/-- Cache the full selected monomial quotient ring. -/
local instance normalizedCoordinatesQuotientRing :
    CommRing (MvPolynomial I
      (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)) ⧸
      chartIdentityIdeal R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)) := inferInstance

/-- A selected monomial, viewed in the ambient truncation of degree d+1. -/
def boundedSelectedMonomial (j : Fin d) : BoundedHilbertMonomials I (d + 1) :=
  ⟨(m j).val, (m j).property.trans (Nat.le_succ d)⟩

/-- The explicit equation imposing a selected identity-matrix entry. -/
def boundedNormalizationEquation (j k : Fin d) : BoundedCoordinateRing R I d :=
  MvPolynomial.X (k, boundedSelectedMonomial I d m j) - if j = k then 1 else 0

/-- The entire selected-column normalization ideal. -/
def boundedNormalizationIdeal : Ideal (BoundedCoordinateRing R I d) :=
  Ideal.span (Set.range fun jk : Fin d × Fin d ↦
    boundedNormalizationEquation R I d m jk.1 jk.2)

/-- The original-base normalized bounded-coordinate algebra. -/
abbrev BoundedNormalizedRing := BoundedCoordinateRing R I d ⧸ boundedNormalizationIdeal R I d m

/-- Selected monomial coordinates in the universal chart are exactly identity entries. -/
theorem chartBoundedCoordinate_selected (j k : Fin d) :
    chartBoundedCoordinate R I d (fun a ↦ MvPolynomial.monomial (m a).val 1) k
        (boundedSelectedMonomial I d m j) = if j = k then 1 else 0 := by
  change (chartIdentityBasis R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)).repr
    (MvPolynomial.aeval _ (MvPolynomial.monomial (m j).val (1 : R))) k = _
  rw [chartIdentityBasis_evaluation, Module.Basis.repr_self_apply]

/-- Every normalization equation vanishes under the actual chart parameter map. -/
theorem boundedNormalizationIdeal_le_ker :
    boundedNormalizationIdeal R I d m ≤ RingHom.ker
      (chartBoundedCoordinateMap R I d
        (fun a ↦ MvPolynomial.monomial (m a).val 1)).toRingHom := by
  rw [boundedNormalizationIdeal, Ideal.span_le]
  rintro _ ⟨⟨j, k⟩, rfl⟩
  change chartBoundedCoordinateMap R I d _ (boundedNormalizationEquation R I d m j k) = 0
  simp only [boundedNormalizationEquation, map_sub, chartBoundedCoordinateMap_X,
    chartBoundedCoordinate_selected]
  split_ifs <;> simp only [map_one, map_zero, sub_self]

/-- The actual chart parameter map factors through all selected normalization equations. -/
def chartNormalizedCoordinateMap : BoundedNormalizedRing R I d m →ₐ[R]
    ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1) :=
  Ideal.Quotient.liftₐ _ (chartBoundedCoordinateMap R I d _)
    (boundedNormalizationIdeal_le_ker R I d m)

/-- Factoring out normalization still recovers every original chart-ring element. -/
theorem chartNormalizedCoordinateMap_surjective :
    Function.Surjective (chartNormalizedCoordinateMap R I d m) := by
  intro z
  obtain ⟨p, hp⟩ := chartBoundedCoordinateMap_surjective R I d
    (fun a ↦ MvPolynomial.monomial (m a).val 1)
    (fun a ↦ (MvPolynomial.totalDegree_monomial_le _ _).trans (m a).property) z
  exact ⟨Ideal.Quotient.mk _ p, hp⟩

end FLT.Mazur.HilbertChart
