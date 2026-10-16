/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNodeBoundedNumerators
public import FLT.Mazur.PolygonSmoothingLaurentReconstruction

/-!
# Full Laurent reconstruction of the retained node-localized numerators

Both branches reconstruct the original chart numerator, and hence the
cleared original node-localized function. This is an equality in the
full rings, retaining all lower coefficients and complete lift choices.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "t" => parameter K m
local notation "L" => originalStageSinglePointLine K n h m i
local notation "N" => completePointStageChartNumerator K n h m i j
local notation "σ" => algebraMap (ChartRing (t)) (StageNodeLocalization K m)
local notation "a" => PolygonInfinitesimal.chartMarkingEquation (Ring K m) (t) n i j 1

/-- Both original Laurent coefficient families reconstruct the entire retained chart numerator. -/
theorem completePointStageNumerator_reconstruction (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    N d s = outgoingPolynomialLift (t) (leftLaurentMap (t) (N d s)) +
      incomingPolynomialLift (t) (precedingLaurentMap (Ring K m) (t) (N d s)) :=
  laurent_reconstruction (t) _

/-- The full reconstructed numerator clears the SAME original node-localized function. -/
theorem completePointNodeLocalized_reconstruction (d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (σ) (a) ^ d * completePointNodeLocalizationMap K n h m i j
        (completePointStageNodeFunction K n h m i j d s) =
      (σ) (outgoingPolynomialLift (t) (leftLaurentMap (t) (N d s))) +
      (σ) (incomingPolynomialLift (t) (precedingLaurentMap (Ring K m) (t) (N d s))) := by
  rw [completePointNodeLocalizedNumerator K n h m i j d hd s]
  calc
    _ = (σ) (outgoingPolynomialLift (t) (leftLaurentMap (t) (N d s)) +
        incomingPolynomialLift (t) (precedingLaurentMap (Ring K m) (t) (N d s))) :=
      congrArg (σ) (completePointStageNumerator_reconstruction K n h m i j d s)
    _ = _ := (σ).map_add _ _

/-- The retained pole-two function uses both original branch coefficient families. -/
theorem completePointNodePoleTwo_reconstruction :
    (σ) (a) ^ 2 * completePointNodeLocalizedPoleTwo K n h m i j =
      (σ) (outgoingPolynomialLift (t) (leftLaurentMap (t)
        (completePointStagePoleTwoChartNumerator K n h m i j))) +
      (σ) (incomingPolynomialLift (t) (precedingLaurentMap (Ring K m) (t)
        (completePointStagePoleTwoChartNumerator K n h m i j))) :=
  completePointNodeLocalized_reconstruction K n h m i j 2 (by decide) _

/-- The retained pole-three function keeps its original lower terms on both branches. -/
theorem completePointNodePoleThree_reconstruction :
    (σ) (a) ^ 3 * completePointNodeLocalizedPoleThree K n h m i j =
      (σ) (outgoingPolynomialLift (t) (leftLaurentMap (t)
        (completePointStagePoleThreeChartNumerator K n h m i j))) +
      (σ) (incomingPolynomialLift (t) (precedingLaurentMap (Ring K m) (t)
        (completePointStagePoleThreeChartNumerator K n h m i j))) :=
  completePointNodeLocalized_reconstruction K n h m i j 3 (by decide) _

end FLT.Mazur.PolygonInfinitesimalStages
