/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNumeratorLaurentBounds

/-!
# Finite original numerators at the first positive-order stage

The retained order-two numerator has five Laurent coefficients and the
order-three numerator has six. These are the original coefficients over
the full first-stage ring, without replacing or normalizing either lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "t" => parameter K 1
local notation "N₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 i i)
local notation "N₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 i i)

/-- The particular retained order-two numerator is its original five-term Laurent sum. -/
theorem completePointFirstPoleTwoLaurent_expansion :
    (N₂) = ∑ k ∈ Finset.Icc (-1 : ℤ) 3, C ((N₂).coeff k) * T k := by
  exact completePointStageNumerator_expansion K n h 1 i 2 (completePointStagePoleTwo K n h 1 i)

/-- The particular retained order-three numerator is its original six-term Laurent sum. -/
theorem completePointFirstPoleThreeLaurent_expansion :
    (N₃) = ∑ k ∈ Finset.Icc (-1 : ℤ) 4, C ((N₃).coeff k) * T k := by
  exact completePointStageNumerator_expansion K n h 1 i 3
    (completePointStagePoleThree K n h 1 i)

/-- Incoming order-two coefficients are the same original coefficients shifted by two. -/
theorem completePointFirstPoleTwoLaurent_incoming (k : ℤ) :
    (precedingLaurentMap (Ring K 1) (t)
      (completePointStagePoleTwoChartNumerator K n h 1 i ((finRotate n).symm i))).coeff k =
      (N₂).coeff (k + 2) := by
  simpa only [completePointStagePoleTwoChartNumerator,
    even_two.neg_pow, one_pow, one_mul, Nat.cast_ofNat] using
    completePointStageNumerator_marked_coefficient K n h 1 i 2
      (completePointStagePoleTwo K n h 1 i) k

/-- Incoming order-three coefficients carry the original negative cubic transition. -/
theorem completePointFirstPoleThreeLaurent_incoming (k : ℤ) :
    (precedingLaurentMap (Ring K 1) (t)
      (completePointStagePoleThreeChartNumerator K n h 1 i ((finRotate n).symm i))).coeff k =
      -(N₃).coeff (k + 3) := by
  simpa only [completePointStagePoleThreeChartNumerator,
    Odd.neg_pow (by decide : Odd 3), one_pow, neg_one_mul, Nat.cast_ofNat] using
    completePointStageNumerator_marked_coefficient K n h 1 i 3
      (completePointStagePoleThree K n h 1 i) k

end FLT.Mazur.PolygonInfinitesimalStages
