/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentFirstStageParameter
public import FLT.Mazur.PolygonCompleteIdentityFirstPositiveNodes

/-!
# The actual first-order action with its universal parameter retained

Move the first input into the first-stage coefficient ring over K[T,T⁻¹].
The unchanged original multiplication is then its original scaling times
a square-zero coordinate with an explicitly computed vector field. This is
an equality for the original unit, not a newly chosen multiplication law.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality PolygonChartScaling
open LaurentFirstStageParameter
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0
local notation "a" => parameterUnit K

/-- The original multiplication unit after retaining its first input in the coefficient ring. -/
def completeIdentityFirstActionUnit : (S)[T;T⁻¹]ˣ :=
  Units.map (coeffMap (parameterEval K)).toMonoidHom
    (completeIdentityFiniteMulUnit K n h i 1)

/-- The retained unit is exactly the original group product on these universal algebra points. -/
theorem completeIdentityFirstActionUnit_point :
    let _ := ((C : (S) →+* (S)[T;T⁻¹]).comp
      (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1)).toAlgebra
    completeIdentityFinitePointMul K n h i 1 (S)[T;T⁻¹]
      (Units.map (C : (S) →+* (S)[T;T⁻¹]).toMonoidHom (a)) (coordinateUnit 1) =
        completeIdentityFirstActionUnit K n h i := by
  dsimp only
  change Units.map
    (LaurentPairNaturality.pairEval₂ (C.comp (stageCoefficientMap (C : K →+* (R)) 1))
      (Units.map (C : (S) →+* (S)[T;T⁻¹]).toMonoidHom (a))
      (coordinateUnit 1)).toMonoidHom _ = _
  rw [parameterEval_pair]
  rfl

/-- The actual action field after removing its prescribed original scaling. -/
def completeIdentityFirstActionField : (R)[T;T⁻¹] :=
  C ((coordinateUnit (1 : Kˣ))⁻¹.val) * (O)

/-- The original action has its exact full first-order error in the unchanged second variable. -/
theorem completeIdentityFirstActionUnit_val :
    (completeIdentityFirstActionUnit K n h i).val = C (a).val * T 1 +
      C (parameter (R) 1) * coeffMap (algebraMap (R) (S)) (O) := by
  have he := congrArg (coeffMap (parameterEval K))
    (completeIdentityFiniteMulDefect_from_obstruction K n h i 0
      (completeIdentityFiniteMulDefect_zero K n h i))
  simp only [completeIdentityFiniteMulDefect, map_sub, map_mul,
    Nat.zero_add, pow_one, coeffMap_C,
    parameterEval_T_one, LaurentCoefficientEvaluation.coeffMap_T,
    parameterEval_doubleLift] at he
  rw [parameterEval_parameter] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- The scaling removed from the field is recovered exactly over the original coefficient ring. -/
theorem completeIdentityFirstActionField_scaled :
    C (a).val * coeffMap (algebraMap (R) (S)) (completeIdentityFirstActionField K n h i) =
      coeffMap (algebraMap (R) (S)) (O) := by
  rw [completeIdentityFirstActionField, map_mul, coeffMap_C, ← mul_assoc, ← map_mul]
  have he : (a).val * algebraMap (R) (S) ((coordinateUnit (1 : Kˣ))⁻¹.val) = 1 := by
    change algebraMap (R) (S) _ * algebraMap (R) (S) _ = 1
    rw [← map_mul, Units.mul_inv, map_one]
  rw [he, map_one, one_mul]

/-- The full original unit is scaling times its computed square-zero field. -/
theorem completeIdentityFirstActionUnit_factor :
    completeIdentityFirstActionUnit K n h i =
      Units.map (C : (S) →+* (S)[T;T⁻¹]).toMonoidHom (a) *
        firstOrderCoordinateUnit (completeIdentityFirstActionField K n h i) := by
  apply Units.ext
  rw [Units.val_mul, firstOrderCoordinateUnit_val, completeIdentityFirstActionUnit_val]
  change _ = C (a).val * (T 1 + C (parameter (R) 1) *
    coeffMap (algebraMap (R) (S)) (completeIdentityFirstActionField K n h i))
  rw [mul_add, mul_left_comm (C (a).val), completeIdentityFirstActionField_scaled]

end FLT.Mazur.PolygonInfinitesimalStages
