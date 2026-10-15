/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstLaurentCoefficient

/-!
# Multiplication on the full first-order Laurent parameter layer

Multiplying a weighted function by an arbitrary branch function depends only
on the latter's reduction. These identities retain both branches and show
that the entire parameter-annihilated pair module has square zero.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "L" => (S)[T;T⁻¹]
local notation "e" => parameter R 1

/-- Reducing a scalar-lifted Laurent function recovers every coefficient. -/
theorem firstLaurent_lift_reduction (p : R[T;T⁻¹]) :
    coeffMap (reduction R 1).toRingHom (coeffMap (algebraMap R (S)) p) = p := by
  ext d
  rw [coeffMap_coeff, coeffMap_coeff]
  exact (reduction R 1).commutes _

/-- Multiplication of a weighted branch function uses only the other's exact reduction. -/
theorem firstLaurentParameterLift_mul (p : R[T;T⁻¹]) (q : L) :
    firstLaurentParameterLift R p * q =
      firstLaurentParameterLift R (p * coeffMap (reduction R 1).toRingHom q) := by
  change C (e) * coeffMap (algebraMap R (S)) p * q = _
  rw [mul_assoc, firstLaurent_parameter_reduction, map_mul, firstLaurent_lift_reduction]
  rfl

/-- Reduction on both complete branches as one ring homomorphism. -/
def firstNodePairReduction : ((L) × (L)) →+* (R[T;T⁻¹] × R[T;T⁻¹]) :=
  (coeffMap (reduction R 1).toRingHom).prodMap (coeffMap (reduction R 1).toRingHom)

/-- Weighting has zero reduction on both full branches. -/
theorem firstNodePairReduction_weighted (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodePairReduction R (firstNodeParameterPair R p) = 0 :=
  Prod.ext (firstLaurentParameterLift_reduction R p.1)
    (firstLaurentParameterLift_reduction R p.2)

/-- Exact multiplication by any full branch pair on the entire weighted submodule. -/
theorem firstNodeParameterPair_mul (p : R[T;T⁻¹] × R[T;T⁻¹]) (q : (L) × (L)) :
    firstNodeParameterPair R p * q =
      firstNodeParameterPair R (p * firstNodePairReduction R q) :=
  Prod.ext (firstLaurentParameterLift_mul R p.1 q.1)
    (firstLaurentParameterLift_mul R p.2 q.2)

/-- The coefficient of a weighted product is its exact reduced product. -/
theorem firstNodePairCoefficient_weighted_mul (p : R[T;T⁻¹] × R[T;T⁻¹]) (q : (L) × (L)) :
    firstNodePairCoefficient R (firstNodeParameterPair R p * q) =
      p * firstNodePairReduction R q := by
  rw [firstNodeParameterPair_mul, firstNodePairCoefficient_weighted]

/-- Multiplication of two arbitrary weighted pairs is zero. -/
theorem firstNodeParameterPair_mul_weighted (p q : R[T;T⁻¹] × R[T;T⁻¹]) :
    firstNodeParameterPair R p * firstNodeParameterPair R q = 0 := by
  rw [firstNodeParameterPair_mul, firstNodePairReduction_weighted, mul_zero, map_zero]

/-- The full parameter annihilator has square zero, without chosen factors. -/
theorem firstNodePair_annihilator_mul (p q : (L) × (L))
    (hp : (e) • p = 0) (hq : (e) • q = 0) : p * q = 0 := by
  rw [← firstNodePairCoefficient_reconstruct R p hp,
    ← firstNodePairCoefficient_reconstruct R q hq]
  exact firstNodeParameterPair_mul_weighted R _ _

/-- Canonical coefficients commute with multiplication on the entire parameter annihilator. -/
theorem firstNodePairCoefficient_mul (p q : (L) × (L)) (hp : (e) • p = 0) :
    firstNodePairCoefficient R (p * q) =
      firstNodePairCoefficient R p * firstNodePairReduction R q := by
  conv_lhs => rw [← firstNodePairCoefficient_reconstruct R p hp]
  exact firstNodePairCoefficient_weighted_mul R _ _

end FLT.Mazur.PolygonInfinitesimalStages
