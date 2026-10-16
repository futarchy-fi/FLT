/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStageFrameUnitProducts
public import FLT.Mazur.PolygonCompletePointFirstMarkingForms

/-!
# One actual marking unit for the original quadratic and cubic numerators

The quotient of the retained cubic and quadratic comparison units has
square and cube equal to those same units. The first-stage numerator
forms use these exact powers and keep every original lower coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "u" => completePointStageArithmeticFrameUnit K n h m i

/-- The common scale is the exact quotient of the two retained comparison units. -/
def completePointStageCommonMarkingUnit : (Ring K m)ˣ := u 3 / u 2

/-- The exact quotient recovers the original quadratic comparison unit by squaring. -/
theorem completePointStageCommonMarkingUnit_sq :
    completePointStageCommonMarkingUnit K n h m i ^ 2 = u 2 := by
  have he : u 3 ^ 2 = u 2 ^ 3 := by
    apply Units.ext
    exact completePointStageArithmeticFrameUnit_three_sq_eq_two_cube K n h m i
  change (u 3 / u 2) ^ 2 = u 2
  rw [div_pow, he, div_eq_iff_eq_mul]
  exact pow_succ' (u 2) 2

/-- Cubing the same exact quotient recovers the original cubic comparison unit. -/
theorem completePointStageCommonMarkingUnit_cube :
    completePointStageCommonMarkingUnit K n h m i ^ 3 = u 3 := by
  calc
    _ = completePointStageCommonMarkingUnit K n h m i ^ 2 *
        completePointStageCommonMarkingUnit K n h m i := pow_succ _ 2
    _ = u 2 * (u 3 / u 2) := congrArg
      (fun z ↦ z * completePointStageCommonMarkingUnit K n h m i)
      (completePointStageCommonMarkingUnit_sq K n h m i)
    _ = u 3 := by rw [← mul_div_assoc, mul_comm (u 2), mul_div_cancel_right]

local notation "t" => parameter K 1
local notation "N₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 i i)
local notation "N₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 i i)
local notation "λ" => (completePointStageCommonMarkingUnit K n h 1 i : Ring K 1)

/-- The unchanged quadratic numerator has the square of the actual common marking unit. -/
theorem completePointFirstPoleTwo_common_unit_form :
    (N₂) = C ((N₂).coeff 2) * (T 1 - 1) ^ 2 + C ((λ) ^ 2) * T 1 := by
  have he := completePointFirstPoleTwo_marking_form K n h i
  rw [completePointStagePoleTwoNumerator_eval_one] at he
  have hu := congrArg (fun z : (Ring K 1)ˣ ↦ (z : Ring K 1))
    (completePointStageCommonMarkingUnit_sq K n h 1 i)
  simpa only [Units.val_pow_eq_pow_val] using he.trans
    (congrArg (fun z : Ring K 1 ↦ C ((N₂).coeff 2) * (T 1 - 1) ^ 2 + C z * T 1) hu.symm)

/-- The unchanged cubic numerator keeps its lower coefficient and the cube of the same unit. -/
theorem completePointFirstPoleThree_common_unit_form :
    (N₃) = C ((N₃).coeff 3) * (T 1 - 1) ^ 3 +
      C ((N₃).coeff 2 + 3 * (N₃).coeff 3) * T 1 * (T 1 - 1) + C ((λ) ^ 3) * T 1 := by
  have he := completePointFirstPoleThree_marking_form K n h i
  rw [completePointStagePoleThreeNumerator_eval_one] at he
  have hu := congrArg (fun z : (Ring K 1)ˣ ↦ (z : Ring K 1))
    (completePointStageCommonMarkingUnit_cube K n h 1 i)
  simpa only [Units.val_pow_eq_pow_val] using he.trans
    (congrArg (fun z : Ring K 1 ↦ C ((N₃).coeff 3) * (T 1 - 1) ^ 3 +
      C ((N₃).coeff 2 + 3 * (N₃).coeff 3) * T 1 * (T 1 - 1) + C z * T 1) hu.symm)

end FLT.Mazur.PolygonInfinitesimalStages
