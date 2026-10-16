/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopOrderBoundaryRigidity
public import FLT.Mazur.LaurentSquareZeroNaturality
public import FLT.Mazur.LaurentSquareZeroReciprocal

/-!
# Both charts of each positive top-weight coordinate unit

The universal square-zero coordinate is a unit. Its value is the top-weight
Laurent coordinate, and its reciprocal in the reciprocal input variable is the
top-weight coordinate of the transformed vector field.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentSquareZeroCoordinate LaurentBoundaryVectorField
open PolygonChartScaling PolygonScalingNaturality LaurentCoefficientEvaluation
variable {R : Type*} [CommRing R] (m : ℕ)

/-- Coefficient change commutes with reciprocal Laurent substitution. -/
theorem topOrder_coeffMap_invert (f : R →+* Ring R (m + 1)) (q : R[T;T⁻¹]) :
    coeffMap f (invert q) = invert (coeffMap f q) := by
  ext d
  simp only [coeffMap_coeff, invert_apply]

/-- The universal unit realizing a vector field at the next positive top layer. -/
def topOrderCoordinateUnit (q : R[T;T⁻¹]) : (Ring R (m + 1))[T;T⁻¹]ˣ :=
  change (C.comp (algebraMap R (Ring R (m + 1))))
    (C (parameter R (m + 1) ^ (m + 1)))
    (by
      rw [← map_pow]
      have he : (parameter R (m + 1) ^ (m + 1)) ^ 2 = 0 := by
        simpa using parameter_top_weight_sq R m (Ring R (m + 1))
      rw [he, map_zero]) q (coordinateUnit 1)

/-- The constructed unit retains the whole top-weight Laurent coordinate. -/
theorem topOrderCoordinateUnit_val (q : R[T;T⁻¹]) :
    (topOrderCoordinateUnit m q).val = topOrderLaurentCoordinate (m + 1) q := by
  exact change_coordinate_one_val (algebraMap R (Ring R (m + 1)))
    (parameter R (m + 1) ^ (m + 1))
    (by simpa using parameter_top_weight_sq R m (Ring R (m + 1))) q

/-- Its inverse has the exact top-weight inverse formula. -/
theorem topOrderCoordinateUnit_inv_val (q : R[T;T⁻¹]) :
    (topOrderCoordinateUnit m q)⁻¹.val =
      T (-1) - C (parameter R (m + 1) ^ (m + 1)) *
        coeffMap (algebraMap R (Ring R (m + 1))) q * T (-2) := by
  change (coordinateUnit (1 : (Ring R (m + 1))ˣ))⁻¹.val -
    C (parameter R (m + 1) ^ (m + 1)) *
      eval₂ (C.comp (algebraMap R (Ring R (m + 1)))) (coordinateUnit 1) q *
        (coordinateUnit (1 : (Ring R (m + 1))ˣ))⁻¹.val ^ 2 = _
  rw [eval₂_coordinate_one]
  simp only [coordinateUnit, Units.val_one, inv_one, map_one, one_mul]
  norm_num

/-- Inverting both output and input gives the polynomial for the reciprocal boundary chart. -/
theorem topOrderCoordinateUnit_reciprocal (q : R[T;T⁻¹]) :
    invert ((topOrderCoordinateUnit m q)⁻¹.val) =
      topOrderLaurentCoordinate (m + 1) (reciprocalField q) := by
  rw [topOrderCoordinateUnit_inv_val]
  simp only [map_sub, map_mul, invert_T, invert_C, topOrderLaurentCoordinate,
    reciprocalField, map_neg, coeffMap_T, topOrder_coeffMap_invert]
  norm_num
  ring

end FLT.Mazur.PolygonInfinitesimalStages
