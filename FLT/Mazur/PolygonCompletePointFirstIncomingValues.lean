/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstUnmarkedIncoming
public import FLT.Mazur.PolygonCompletePointCommonMarkingUnit

/-!
# Exact incoming coefficients of the retained quadratic and cubic

The two-cycle correction uses the actual common marking unit in degree two
and the unchanged lower cubic coefficient in degree three. Away from the
two-cycle the same incoming coefficients vanish in the full first-stage ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Scheme.Modules
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "t" => parameter K 1
local notation "N₂" => completePointStagePoleTwoChartNumerator K n h 1 i i
local notation "N₃" => completePointStagePoleThreeChartNumerator K n h 1 i i
local notation "P₂" => leftLaurentMap (t) (N₂)
local notation "P₃" => leftLaurentMap (t) (N₃)
local notation "λ" => (completePointStageCommonMarkingUnit K n h 1 i : Ring K 1)
local notation "twoCycle" => Equiv.symm (finRotate n) (Equiv.symm (finRotate n) i) = i

/-- The retained linear and quadratic coefficients sum to the exact common-unit square. -/
theorem completePointFirstPoleTwo_coefficient_unit :
    (P₂).coeff 1 + 2 * (P₂).coeff 2 = (λ) ^ 2 := by
  have he := completePointFirstPoleTwo_marking_value K n h i
  rw [completePointStagePoleTwoNumerator_eval_one] at he
  have hu := congrArg (fun z : (Ring K 1)ˣ ↦ (z : Ring K 1))
    (completePointStageCommonMarkingUnit_sq K n h 1 i)
  simpa only [Units.val_pow_eq_pow_val, add_comm] using he.symm.trans hu.symm

/-- The unchanged two middle cubic coefficients sum to the exact common-unit cube. -/
theorem completePointFirstPoleThree_coefficient_unit :
    (P₃).coeff 1 + (P₃).coeff 2 = (λ) ^ 3 := by
  have he := completePointFirstPoleThree_marking_value K n h i
  rw [completePointStagePoleThreeNumerator_eval_one] at he
  have hu := congrArg (fun z : (Ring K 1)ˣ ↦ (z : Ring K 1))
    (completePointStageCommonMarkingUnit_cube K n h 1 i)
  simpa only [Units.val_pow_eq_pow_val] using he.symm.trans hu.symm

/-- The original quadratic incoming coefficient keeps the precise two-cycle correction. -/
theorem completePointFirstPoleTwo_incoming_value :
    (precedingLaurentMap (Ring K 1) (t) (N₂)).coeff (-1) =
      if twoCycle then (t) * (λ) ^ 2 else 0 := by
  by_cases hc : twoCycle
  · rw [ite_eq_left hc]
    have he := completePointFirstNumerator_twoCycle_incoming K n h i hc 2
      (completePointStagePoleTwo K n h 1 i)
    simp only [even_two.neg_pow, one_pow, one_mul, Nat.cast_ofNat, Int.reduceSub] at he
    exact he.trans (congrArg (fun z : Ring K 1 ↦ (t) * z)
      (completePointFirstPoleTwo_coefficient_unit K n h i))
  · rw [ite_eq_right hc]
    exact completePointFirstNumerator_incoming_of_not_twoCycle K n h i hc 2 _

/-- The cubic correction retains its original lower coefficient and its original sign. -/
theorem completePointFirstPoleThree_incoming_value :
    (precedingLaurentMap (Ring K 1) (t) (N₃)).coeff (-1) =
      if twoCycle then -(t) * ((P₃).coeff 2 + 3 * (P₃).coeff 3) else 0 := by
  by_cases hc : twoCycle
  · rw [ite_eq_left hc]
    simpa only [completePointStagePoleThreeChartNumerator, Odd.neg_pow (by decide : Odd 3),
      one_pow, neg_one_mul,
      Nat.cast_ofNat, Int.reduceSub] using
      completePointFirstNumerator_twoCycle_incoming K n h i hc 3
        (completePointStagePoleThree K n h 1 i)
  · rw [ite_eq_right hc]
    exact completePointFirstNumerator_incoming_of_not_twoCycle K n h i hc 3 _

end FLT.Mazur.PolygonInfinitesimalStages
