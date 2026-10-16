/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDivisorEquationFrameTransport
public import FLT.Mazur.PolygonCompletePointStageEquationFrames

/-!
# The original chart numerator in the actual equation frame

The specified image-open marking equation maps to the same arithmetic
equation. Canonical-section preservation therefore identifies the frame
coordinate of each retained global section with its original numerator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback
open AffineImmersionSectionCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "t" => parameter K m
local notation "f" => PolygonInfinitesimal.chart (Ring K m) (t) n h i
local notation "L" => originalStageSinglePointLine K n h m i
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)
local notation "a" => CommRingCat.Hom.hom
  (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of (ChartRing (t)))))
  (PolygonInfinitesimal.chartMarkingEquation (Ring K m) (t) n i i 1)
local notation "g" => PolygonInfinitesimal.markingImageEquation (Ring K m) (t) n h i i 1

omit [NeZero n] in
/-- The image-open equation pulls to exactly the specified chart equation. -/
theorem completePointMarkingImageEquation_app : ((f).appIso ⊤).hom (g) = (a) := by
  let e := (Scheme.ΓSpecIso (.of (ChartRing (t)))).commRingCatIsoToRingEquiv
  apply e.injective
  change coordinates (f) (g) = e (e.symm _)
  rw [PolygonInfinitesimal.markingImageEquation_coordinate, RingEquiv.apply_symm_apply]

/-- The actual chart equation frame retains the canonical tensor section. -/
theorem completePointStageChartEquationFrame_canonical (d : ℕ) :
    (completePointStageChartEquationFrame K n h m i d).hom.app ⊤
      (pullGlobal (f) _ (tensorPowerSection (L) ⊤ (divisorSection (hI) ⊤) d)) =
        (a) ^ d := by
  let _ : IsAffine (PolygonSmoothing.chart (Ring K m) (t)) :=
    inferInstanceAs (IsAffine (Spec (.of (ChartRing (t)))))
  rw [completePointStageChartEquationFrame_def]
  exact divisorPulledEquationFrame_canonical (f) (hI) _ _
    (divisorLinePullbackIsoOfEq_compatible (f) (hI) _ rfl) (a) _ _ d

/-- The specified chart frame returns precisely the original image-open numerator. -/
theorem completePointStageChartEquationFrame_numerator (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    (Scheme.ΓSpecIso (.of (ChartRing (t)))).hom
      ((completePointStageChartEquationFrame K n h m i d).hom.app ⊤
        (pullGlobal (f) _ s)) = completePointStageChartNumerator K n h m i i d s := by
  have hc : (completePointStageChartEquationFrame K n h m i d).hom.app ⊤
      (pullGlobal (f) _ (tensorPowerSection (L) ⊤ (divisorSection (hI) ⊤) d)) =
        (((f).appIso ⊤).hom (g) : Γ(Spec (.of (ChartRing (t))), ⊤)) ^ d := by
    rw [completePointMarkingImageEquation_app]
    exact completePointStageChartEquationFrame_canonical K n h m i d
  have hn := divisorChartFrame_numerator (f) (hI) (g)
    (PolygonInfinitesimal.markingImageEquation_regular (Ring K m) (t) n h i i 1)
    (PolygonInfinitesimal.markingImageIdeal_equation (Ring K m) (t) n h i i 1)
    d (completePointStageChartEquationFrame K n h m i d) hc s
  rw [completePointStageChartNumerator_def]
  exact congrArg (Scheme.ΓSpecIso (.of (ChartRing (t)))).hom hn

end FLT.Mazur.PolygonInfinitesimalStages
