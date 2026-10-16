/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorAffineLocalizedNumerator
public import FLT.Mazur.PolygonCompletePointStageBoundedNumerators
public import FLT.Mazur.PolygonCompletePointNodeLocalization

/-!
# Exact pole-degree bounds for the retained node-localized functions

The actual full-stage chart equation clears each original localized function
in its original degree. Both the retained sections and all numerator coefficients
are unchanged, including at the first positive-order stage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve AffineImmersionSectionCoordinates
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "f" => PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j
local notation "C" => GlobalIdealPowerCompatibility.complement
  (Scheme.Hom.ker (marking K m n h i))
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)
local notation "L" => originalStageSinglePointLine K n h m i
local notation "σ" => algebraMap (ChartRing (parameter K m)) (StageNodeLocalization K m)
local notation "g" => PolygonInfinitesimal.markingImageEquation
  (Ring K m) (parameter K m) n h i j 1
local notation "a" => PolygonInfinitesimal.chartMarkingEquation
  (Ring K m) (parameter K m) n i j 1

/-- The original degree bounds the denominator of the very same node-localized section. -/
theorem completePointNodeLocalizedNumerator (d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (σ) (a) ^ d * completePointNodeLocalizationMap K n h m i j
      (completePointStageNodeFunction K n h m i j d s) =
      (σ) (completePointStageChartNumerator K n h m i j d s) := by
  let q := completePointNodeLocalizationChart K n h m i j ≫ ((f) ∣_ (C))
  have hq : Spec.map (CommRingCat.ofHom (σ)) ≫ (f) = q ≫ (C).ι := by
    dsimp only [q]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ (f))
      (completePointNodeLocalizationChart_ι K n h m i j).symm
  have he := divisorAffineLocalizedNumerator hI (f) (g)
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (parameter K m) n h i j 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (parameter K m) n h i j 1)
    (σ) q hq d hd s
  have hg : coordinates (f) (g) = (a) :=
    PolygonInfinitesimal.markingImageEquation_coordinate (Ring K m)
      (parameter K m) n h i j 1
  erw [hg] at he
  rw [completePointStageChartNumerator_def]
  exact he

/-- The square of the specified marking equation clears the retained order-two function. -/
theorem completePointNodeLocalizedPoleTwo_bounded :
    (σ) (a) ^ 2 * completePointNodeLocalizedPoleTwo K n h m i j =
      (σ) (completePointStagePoleTwoChartNumerator K n h m i j) :=
  completePointNodeLocalizedNumerator K n h m i j 2 (by decide) _

/-- The cube of that same equation clears the retained order-three function. -/
theorem completePointNodeLocalizedPoleThree_bounded :
    (σ) (a) ^ 3 * completePointNodeLocalizedPoleThree K n h m i j =
      (σ) (completePointStagePoleThreeChartNumerator K n h m i j) :=
  completePointNodeLocalizedNumerator K n h m i j 3 (by decide) _

end FLT.Mazur.PolygonInfinitesimalStages
