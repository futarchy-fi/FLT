/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStageBoundedNumerators
public import FLT.Mazur.DivisorChartPoleRatio

/-!
# Bounded canonical pole ratios on original arithmetic chart images

The original marking equation to degree d clears the actual canonical ratio
of each retained degree-d section. The numerator is the specified original
chart numerator, including every lower coefficient.
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
local notation "C" => GlobalIdealPowerCompatibility.complement
  (Scheme.Hom.ker (marking K m n h i))

/-- The actual chart image minus this one original global marking. -/
def completePointStagePoleImageOpen : (family K m n h).left.Opens := (U).1 ⊓ (C)

/-- Every actual retained section has its specified degree-bounded canonical ratio. -/
theorem completePointStageChartNumerator_ratio (d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (L) d, ⊤)) :
    let V := completePointStagePoleImageOpen K n h m i j
    let c := tensorPowerSection (L) ⊤ (divisorSection hI ⊤) d
    ((family K m n h).left.presheaf.map (homOfLE (show V ≤ (U).1 from inf_le_left)).op
      (g)) ^ d *
      sectionRatioOn (tensorPower (L) d) c V
        (inf_le_right.trans (divisorComplement_le_powerGenerator hI d hd)) s =
      (family K m n h).left.presheaf.map (homOfLE (show V ≤ (U).1 from inf_le_left)).op
        ((coordinates (f)).symm (completePointStageChartNumerator K n h m i j d s)) := by
  dsimp only
  rw [completePointStageChartNumerator_def, RingEquiv.symm_apply_apply]
  exact divisorChartTensorNumerator_complement_ratio hI (U) (g)
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (parameter K m) n h i j 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (parameter K m) n h i j 1)
    d hd _ inf_le_left inf_le_right s

end FLT.Mazur.PolygonInfinitesimalStages
