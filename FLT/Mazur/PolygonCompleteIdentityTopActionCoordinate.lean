/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentStageParameter
public import FLT.Mazur.PolygonTopOrderCoordinateCharts
public import FLT.Mazur.PolygonCompleteIdentityFirstPositiveNodes

/-!
# The actual top-order action with its universal parameter retained

Move the first input into the next-stage coefficient ring over K[T,T⁻¹].
The unchanged original multiplication is then its original scaling times
a square-zero coordinate with an explicitly computed vector field. This is
an equality for the original unit, not a newly chosen multiplication law.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality PolygonChartScaling
open LaurentStageParameter
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) (m + 1)
local notation "O" => completeIdentityFiniteMulObstruction K n h i m
local notation "a" => parameterUnit K (m + 1)

/-- The original multiplication unit after retaining its first input in the coefficient ring. -/
def completeIdentityTopActionUnit : (S)[T;T⁻¹]ˣ :=
  Units.map (coeffMap (parameterEval K (m + 1))).toMonoidHom
    (completeIdentityFiniteMulUnit K n h i (m + 1))

/-- The retained unit is exactly the original group product on these universal algebra points. -/
theorem completeIdentityTopActionUnit_point :
    let _ := ((C : (S) →+* (S)[T;T⁻¹]).comp
      (stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1))).toAlgebra
    completeIdentityFinitePointMul K n h i (m + 1) (S)[T;T⁻¹]
      (Units.map (C : (S) →+* (S)[T;T⁻¹]).toMonoidHom (a)) (coordinateUnit 1) =
        completeIdentityTopActionUnit K n h i m := by
  dsimp only
  change Units.map
    (LaurentPairNaturality.pairEval₂ (C.comp (stageCoefficientMap (C : K →+* (R)) (m + 1)))
      (Units.map (C : (S) →+* (S)[T;T⁻¹]).toMonoidHom (a))
      (coordinateUnit 1)).toMonoidHom _ = _
  rw [parameterEval_pair]
  rfl

/-- The actual action field after removing its prescribed original scaling. -/
def completeIdentityTopActionField : (R)[T;T⁻¹] :=
  C ((coordinateUnit (1 : Kˣ))⁻¹.val) * (O)

/-- The original action has its exact full top-order error in the unchanged second variable. -/
theorem completeIdentityTopActionUnit_val
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) :
    (completeIdentityTopActionUnit K n h i m).val = C (a).val * T 1 +
      C (parameter (R) (m + 1) ^ (m + 1)) * coeffMap (algebraMap (R) (S)) (O) := by
  have he := congrArg (coeffMap (parameterEval K (m + 1)))
    (completeIdentityFiniteMulDefect_from_obstruction K n h i m hm)
  simp only [completeIdentityFiniteMulDefect, map_sub, map_mul,
    map_pow, coeffMap_C,
    parameterEval_T_one, LaurentCoefficientEvaluation.coeffMap_T,
    parameterEval_doubleLift] at he
  rw [parameterEval_parameter, ← map_pow] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- The scaling removed from the field is recovered exactly over the original coefficient ring. -/
theorem completeIdentityTopActionField_scaled :
    C (a).val * coeffMap (algebraMap (R) (S)) (completeIdentityTopActionField K n h i m) =
      coeffMap (algebraMap (R) (S)) (O) := by
  rw [completeIdentityTopActionField, map_mul, coeffMap_C, ← mul_assoc, ← map_mul]
  have he : (a).val * algebraMap (R) (S) ((coordinateUnit (1 : Kˣ))⁻¹.val) = 1 := by
    change algebraMap (R) (S) _ * algebraMap (R) (S) _ = 1
    rw [← map_mul, Units.mul_inv, map_one]
  rw [he, map_one, one_mul]

/-- The full original unit is scaling times its computed square-zero field. -/
theorem completeIdentityTopActionUnit_factor
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) :
    completeIdentityTopActionUnit K n h i m =
      Units.map (C : (S) →+* (S)[T;T⁻¹]).toMonoidHom (a) *
        topOrderCoordinateUnit m (completeIdentityTopActionField K n h i m) := by
  apply Units.ext
  rw [Units.val_mul, topOrderCoordinateUnit_val, topOrderLaurentCoordinate,
    completeIdentityTopActionUnit_val K n h i m hm]
  change _ = C (a).val * (T 1 + C (parameter (R) (m + 1) ^ (m + 1)) *
    coeffMap (algebraMap (R) (S)) (completeIdentityTopActionField K n h i m))
  rw [mul_add, mul_left_comm (C (a).val), completeIdentityTopActionField_scaled]

end FLT.Mazur.PolygonInfinitesimalStages
