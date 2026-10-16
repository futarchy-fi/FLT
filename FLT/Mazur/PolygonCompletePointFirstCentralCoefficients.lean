/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstEndpointCoefficients

/-!
# Retained quadratic and cubic coefficient formulas

The full-cycle endpoint relation removes one coefficient from each original
numerator. Evaluation at T=1 is kept as its actual ring element, without
identifying the chart equation frame with the retained complete pole frame.
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
local notation "N₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 i i)
local notation "N₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 i i)

/-- The retained quadratic numerator has two independent original coefficients. -/
theorem completePointFirstPoleTwo_polynomial :
    (N₂) = C ((N₂).coeff 2) + C ((N₂).coeff 1) * T 1 + C ((N₂).coeff 2) * T 2 := by
  have he := completePointFirstNumerator_degree_expansion K n h i 2
    (completePointStagePoleTwo K n h 1 i)
  have hi : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by decide
  rw [Nat.cast_ofNat, hi] at he
  simp only [Finset.mem_insert, zero_ne_one, Finset.mem_singleton, OfNat.zero_ne_ofNat,
    or_self, not_false_eq_true, Finset.sum_insert, T_zero, mul_one, OfNat.one_ne_ofNat,
    Finset.sum_singleton] at he
  change (N₂) = _ at he
  rw [completePointFirstPoleTwo_endpoints K n h i] at he
  simpa only [add_assoc, completePointStagePoleTwoChartNumerator] using he

/-- The retained cubic numerator has three independent original coefficients. -/
theorem completePointFirstPoleThree_polynomial :
    (N₃) = -C ((N₃).coeff 3) + C ((N₃).coeff 1) * T 1 +
      C ((N₃).coeff 2) * T 2 + C ((N₃).coeff 3) * T 3 := by
  have he := completePointFirstNumerator_degree_expansion K n h i 3
    (completePointStagePoleThree K n h 1 i)
  have hi : Finset.Icc (0 : ℤ) 3 = {0, 1, 2, 3} := by decide
  rw [Nat.cast_ofNat, hi] at he
  simp only [Finset.mem_insert, zero_ne_one, OfNat.zero_ne_ofNat, Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.sum_insert, T_zero, mul_one, OfNat.one_ne_ofNat,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, Finset.sum_singleton] at he
  change (N₃) = _ at he
  rw [completePointFirstPoleThree_endpoints K n h i, map_neg] at he
  simpa only [add_assoc, completePointStagePoleThreeChartNumerator] using he

/-- Evaluation uses the chart numerator's actual quadratic coefficient sum. -/
theorem completePointFirstPoleTwo_marking_value :
    eval₂ (RingHom.id (Ring K 1)) 1 (N₂) = 2 * (N₂).coeff 2 + (N₂).coeff 1 := by
  conv_lhs => rw [completePointFirstPoleTwo_polynomial K n h i]
  simp only [map_add, eval₂_C, eval₂_C_mul_T, RingHom.id_apply,
    one_zpow, Units.val_one, mul_one]
  ring

/-- Evaluation uses the chart numerator's actual cubic coefficient sum. -/
theorem completePointFirstPoleThree_marking_value :
    eval₂ (RingHom.id (Ring K 1)) 1 (N₃) = (N₃).coeff 1 + (N₃).coeff 2 := by
  conv_lhs => rw [completePointFirstPoleThree_polynomial K n h i]
  simp only [map_add, map_neg, eval₂_C, eval₂_C_mul_T, RingHom.id_apply,
    one_zpow, Units.val_one, mul_one]
  ring

end FLT.Mazur.PolygonInfinitesimalStages
