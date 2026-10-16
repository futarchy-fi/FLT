/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNodeBoundedNumerators

/-!
# The original pole equations on every labeled node chart

The outgoing equation is x-1, the incoming equation is y-1, and all other
charts have denominator one. These formulas retain every stage coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "σ" => algebraMap (ChartRing (parameter K m)) (StageNodeLocalization K m)

/-- On its own full chart, the retained order-two function has denominator (x-1)^2. -/
theorem completePointNodePoleTwo_own_equation :
    ((σ) (leftCoordinate (parameter K m)) - 1) ^ 2 *
      completePointNodeLocalizedPoleTwo K n h m i i =
      (σ) (completePointStagePoleTwoChartNumerator K n h m i i) := by
  simpa only [PolygonInfinitesimal.chartMarkingEquation, ite_true,
    Units.val_one, map_one, map_sub] using
    completePointNodeLocalizedPoleTwo_bounded K n h m i i

/-- On its own full chart, the retained order-three function has denominator (x-1)^3. -/
theorem completePointNodePoleThree_own_equation :
    ((σ) (leftCoordinate (parameter K m)) - 1) ^ 3 *
      completePointNodeLocalizedPoleThree K n h m i i =
      (σ) (completePointStagePoleThreeChartNumerator K n h m i i) := by
  simpa only [PolygonInfinitesimal.chartMarkingEquation, ite_true,
    Units.val_one, map_one, map_sub] using
    completePointNodeLocalizedPoleThree_bounded K n h m i i

/-- The original incoming order-two denominator is exactly (y-1)^2, also for n=2. -/
theorem completePointNodePoleTwo_preceding_equation :
    ((σ) (rightCoordinate (parameter K m)) - 1) ^ 2 *
      completePointNodeLocalizedPoleTwo K n h m i ((finRotate n).symm i) =
      (σ) (completePointStagePoleTwoChartNumerator K n h m i ((finRotate n).symm i)) := by
  simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
    ite_false, ite_true, inv_one, Units.val_one, map_one, map_sub] using
    completePointNodeLocalizedPoleTwo_bounded K n h m i ((finRotate n).symm i)

/-- The original incoming order-three denominator is exactly (y-1)^3. -/
theorem completePointNodePoleThree_preceding_equation :
    ((σ) (rightCoordinate (parameter K m)) - 1) ^ 3 *
      completePointNodeLocalizedPoleThree K n h m i ((finRotate n).symm i) =
      (σ) (completePointStagePoleThreeChartNumerator K n h m i ((finRotate n).symm i)) := by
  simpa only [PolygonInfinitesimal.chartMarkingEquation, PolygonCyclicAtlas.prev_ne h i,
    ite_false, ite_true, inv_one, Units.val_one, map_one, map_sub] using
    completePointNodeLocalizedPoleThree_bounded K n h m i ((finRotate n).symm i)

/-- Every other retained order-two function is the image of its original chart numerator. -/
theorem completePointNodePoleTwo_other_equation
    (hji : j ≠ i) (hjp : j ≠ (finRotate n).symm i) :
    completePointNodeLocalizedPoleTwo K n h m i j =
      (σ) (completePointStagePoleTwoChartNumerator K n h m i j) := by
  simpa only [PolygonInfinitesimal.chartMarkingEquation, hji, hjp,
    ite_false, map_one, one_pow, one_mul] using
    completePointNodeLocalizedPoleTwo_bounded K n h m i j

/-- Every other retained order-three function has no marking denominator on this chart. -/
theorem completePointNodePoleThree_other_equation
    (hji : j ≠ i) (hjp : j ≠ (finRotate n).symm i) :
    completePointNodeLocalizedPoleThree K n h m i j =
      (σ) (completePointStagePoleThreeChartNumerator K n h m i j) := by
  simpa only [PolygonInfinitesimal.chartMarkingEquation, hji, hjp,
    ite_false, map_one, one_pow, one_mul] using
    completePointNodeLocalizedPoleThree_bounded K n h m i j

end FLT.Mazur.PolygonInfinitesimalStages
