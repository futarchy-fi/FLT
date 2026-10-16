/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalMarkingImageEquation
public import FLT.Mazur.PolygonCompletePointStagePoleSections
public import FLT.Mazur.DivisorChartTensorNumerator

/-!
# Bounded chart numerators of the retained complete pole sections

The original full-stage marking equation clears an actual degree-d tensor
section with exponent d. The numerator uses the retained section and the
specified original equation; no replacement lift or normalized lower term is chosen.
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
local notation "U" => imageAffine (f)
local notation "g" => PolygonInfinitesimal.markingImageEquation
  (Ring K m) (parameter K m) n h i j 1
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)
local notation "L" => originalStageSinglePointLine K n h m i

/-- The actual numerator in the original full-stage chart ring, in its original degree. -/
irreducible_def completePointStageChartNumerator (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) : ChartRing (parameter K m) :=
  coordinates (f) (divisorChartTensorNumerator hI (U) (g)
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (parameter K m) n h i j 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (parameter K m) n h i j 1)
    d ((tensorPower (L) d).presheaf.map (U).1.leTop.op s))

/-- The specified degree clears the SAME retained section on the full original chart image. -/
theorem completePointStageChartNumerator_smul (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (g) ^ d • (tensorPower (L) d).presheaf.map (U).1.leTop.op s =
      (coordinates (f)).symm (completePointStageChartNumerator K n h m i j d s) •
        tensorPowerSection (L) (U).1 (divisorSection hI (U).1) d := by
  rw [completePointStageChartNumerator_def, RingEquiv.symm_apply_apply]
  exact divisorChartTensorNumerator_smul hI (U) (g)
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (parameter K m) n h i j 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (parameter K m) n h i j 1) d _

/-- The particular retained pole-two section's bounded original numerator. -/
def completePointStagePoleTwoChartNumerator : ChartRing (parameter K m) :=
  completePointStageChartNumerator K n h m i j 2 (completePointStagePoleTwo K n h m i)

/-- The particular retained pole-three section's bounded original numerator. -/
def completePointStagePoleThreeChartNumerator : ChartRing (parameter K m) :=
  completePointStageChartNumerator K n h m i j 3 (completePointStagePoleThree K n h m i)

/-- Exactly the square of the original equation clears the retained pole-two section. -/
theorem completePointStagePoleTwoChartNumerator_smul :
    (g) ^ 2 • (tensorPower (L) 2).presheaf.map (U).1.leTop.op
      (completePointStagePoleTwo K n h m i) =
      (coordinates (f)).symm (completePointStagePoleTwoChartNumerator K n h m i j) •
        tensorPowerSection (L) (U).1 (divisorSection hI (U).1) 2 :=
  completePointStageChartNumerator_smul K n h m i j 2 _

/-- Exactly the cube of the original equation clears the retained pole-three section. -/
theorem completePointStagePoleThreeChartNumerator_smul :
    (g) ^ 3 • (tensorPower (L) 3).presheaf.map (U).1.leTop.op
      (completePointStagePoleThree K n h m i) =
      (coordinates (f)).symm (completePointStagePoleThreeChartNumerator K n h m i j) •
        tensorPowerSection (L) (U).1 (divisorSection hI (U).1) 3 :=
  completePointStageChartNumerator_smul K n h m i j 3 _

end FLT.Mazur.PolygonInfinitesimalStages
