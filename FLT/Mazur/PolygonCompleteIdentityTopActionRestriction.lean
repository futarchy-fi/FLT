/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopActionCoordinate

/-!
# Adjacent restriction of the full original action

Once the preceding original law holds, both full branch coordinates
restrict to their prescribed reciprocal scalings. The second coordinate
is the reciprocal of the unchanged action in the reciprocal input.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentStageParameter LaurentBoundaryVectorField PolygonChartScaling
open PolygonScalingNaturality LaurentCoefficientEvaluation
attribute [local irreducible] completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) (m + 1)
local notation "a" => parameterUnit K (m + 1)
local notation "U" => completeIdentityTopActionUnit K n h i m
local notation "F" => completeIdentityTopActionField K n h i m

/-- The actual action in the reciprocal input and output coordinates. -/
def completeIdentityTopActionReciprocalUnit : (S)[T;T⁻¹]ˣ :=
  Units.map invert.toMonoidHom (U)⁻¹

variable (hm : completeIdentityFiniteMulDefect K n h i m = 0)
include hm

/-- Exact factorization of the reciprocal original action at the top weight. -/
theorem completeIdentityTopActionUnit_reciprocal :
    invert (U)⁻¹.val = C (a)⁻¹.val *
      topOrderLaurentCoordinate (m + 1) (reciprocalField (F)) := by
  rw [completeIdentityTopActionUnit_factor K n h i m hm, mul_inv_rev, Units.val_mul,
    map_mul, topOrderCoordinateUnit_reciprocal]
  change _ * invert (C (a)⁻¹.val) = _
  rw [invert_C, mul_comm]

/-- The unchanged action has exactly its original scaling at the preceding stage. -/
theorem completeIdentityTopActionUnit_restriction :
    coeffMap (restriction (R) m).toRingHom (U).val =
      C (restriction (R) m (a).val) * T 1 := by
  rw [completeIdentityTopActionUnit_val K n h i m hm]
  have he : (restriction (R) m).toRingHom
      (parameter (R) (m + 1) ^ (m + 1)) = 0 := by
    change restriction (R) m _ = 0
    rw [map_pow, restriction_parameter, parameter_pow]
  simp only [map_add, map_mul, coeffMap_C, coeffMap_T, he, map_zero, zero_mul, add_zero]
  rfl

/-- The reciprocal original action retains the full inverse scaling at the preceding stage. -/
theorem completeIdentityTopActionReciprocalUnit_restriction :
    coeffMap (restriction (R) m).toRingHom
        (completeIdentityTopActionReciprocalUnit K n h i m).val =
      C (restriction (R) m (a)⁻¹.val) * T 1 := by
  change coeffMap (restriction (R) m).toRingHom (invert (U)⁻¹.val) = _
  rw [completeIdentityTopActionUnit_reciprocal K n h i m hm, topOrderLaurentCoordinate]
  have he : (restriction (R) m).toRingHom
      (parameter (R) (m + 1) ^ (m + 1)) = 0 := by
    change restriction (R) m _ = 0
    rw [map_pow, restriction_parameter, parameter_pow]
  simp only [map_add, map_mul, coeffMap_C, coeffMap_T, he, map_zero, zero_mul, add_zero]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
