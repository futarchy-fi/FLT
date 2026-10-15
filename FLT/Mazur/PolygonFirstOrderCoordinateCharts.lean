/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstOrderBoundaryRigidity
public import FLT.Mazur.LaurentSquareZeroNaturality
public import FLT.Mazur.LaurentSquareZeroReciprocal

/-!
# Both charts of the actual first-order coordinate unit

The universal square-zero coordinate is a unit. Its value is the first-order
Laurent coordinate, and its reciprocal in the reciprocal input variable is the
first-order coordinate of the transformed vector field.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentSquareZeroCoordinate LaurentBoundaryVectorField
open PolygonChartScaling PolygonScalingNaturality LaurentCoefficientEvaluation
variable {R : Type*} [CommRing R]

/-- Coefficient change commutes with reciprocal Laurent substitution. -/
theorem firstOrder_coeffMap_invert (f : R →+* Ring R 1) (q : R[T;T⁻¹]) :
    coeffMap f (invert q) = invert (coeffMap f q) := by
  ext d
  simp only [coeffMap_coeff, invert_apply]

/-- The universal unit realizing a vector field on the actual first smoothing stage. -/
def firstOrderCoordinateUnit (q : R[T;T⁻¹]) : (Ring R 1)[T;T⁻¹]ˣ :=
  change (C.comp (algebraMap R (Ring R 1))) (C (parameter R 1))
    (by rw [← map_pow, parameter_pow R 1, map_zero]) q (coordinateUnit 1)

/-- The constructed unit retains the whole first-order Laurent coordinate. -/
theorem firstOrderCoordinateUnit_val (q : R[T;T⁻¹]) :
    (firstOrderCoordinateUnit q).val = firstOrderLaurentCoordinate q :=
  change_coordinate_one_val (algebraMap R (Ring R 1)) (parameter R 1) (parameter_pow R 1) q

/-- Its inverse has the exact first-order inverse formula. -/
theorem firstOrderCoordinateUnit_inv_val (q : R[T;T⁻¹]) :
    (firstOrderCoordinateUnit q)⁻¹.val =
      T (-1) - C (parameter R 1) * coeffMap (algebraMap R (Ring R 1)) q * T (-2) := by
  change (coordinateUnit (1 : (Ring R 1)ˣ))⁻¹.val -
    C (parameter R 1) *
      eval₂ (C.comp (algebraMap R (Ring R 1))) (coordinateUnit 1) q *
        (coordinateUnit (1 : (Ring R 1)ˣ))⁻¹.val ^ 2 = _
  rw [eval₂_coordinate_one]
  simp only [coordinateUnit, Units.val_one, inv_one, map_one, one_mul]
  norm_num

/-- Inverting both output and input gives the polynomial for the reciprocal boundary chart. -/
theorem firstOrderCoordinateUnit_reciprocal (q : R[T;T⁻¹]) :
    invert ((firstOrderCoordinateUnit q)⁻¹.val) =
      firstOrderLaurentCoordinate (reciprocalField q) := by
  rw [firstOrderCoordinateUnit_inv_val]
  simp only [map_sub, map_mul, invert_T, invert_C, firstOrderLaurentCoordinate,
    reciprocalField, map_neg, coeffMap_T, firstOrder_coeffMap_invert]
  norm_num
  ring

end FLT.Mazur.PolygonInfinitesimalStages
