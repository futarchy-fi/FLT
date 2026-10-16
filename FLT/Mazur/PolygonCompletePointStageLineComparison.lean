/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianPointLine
public import FLT.Mazur.PolygonCompleteStageMarkings

/-!
# The original single-point pole line at every full infinitesimal stage

The complete pole line restricts to the divisor line of the same original
finite-stage marking, retaining its canonical section and all nilpotents.
This provides the line comparison needed to express the chosen complete pole
sections in original first-stage node coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  family originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)

/-- The unchanged single stage marking is relatively Cartier, including at positive order. -/
theorem originalStageSingleMarking_relativeCartier :
    RelativeEffectiveCartier (family K m n h).hom (marking K m n h i).ker := by
  simpa only [completeCartesianMarking_originalStage] using
    completeCartesianMarking_relativeCartier K n h (baseToSeries K m)
      (originalStageToCompatibleProj K n h m) (family K m n h).hom
      (originalStageToCompatibleProj_isPullback K n h m) i

/-- The pole line of one original marking on the full finite stage. -/
def originalStageSinglePointLine : (family K m n h).left.Modules :=
  divisorLineBundle (marking K m n h i).ker
    (originalStageSingleMarking_relativeCartier K n h m i).1

/-- The complete single-point pole line restricts to the original finite-stage divisor line. -/
def completePointLineOriginalStageIso :
    (Scheme.Modules.pullback (originalStageToCompatibleProj K n h m)).obj
      (completePointLine K n h i) ≅ originalStageSinglePointLine K n h m i := by
  let _ := completeCartesianPointIdeal_isIso K n h (baseToSeries K m)
    (originalStageToCompatibleProj K n h m) (family K m n h).hom
    (originalStageToCompatibleProj_isPullback K n h m) i
  exact divisorLinePullbackIsoOfEq _ (completeBaseMarking_relativeCartier K n h i).1
    (originalStageSingleMarking_relativeCartier K n h m i).1
    (completeBaseMarking_ker_originalStage K n h m i)

/-- The stage comparison retains the literal canonical section of the same original marking. -/
@[reassoc] theorem completePointLineOriginalStageIso_section :
    (Scheme.Modules.pullback (originalStageToCompatibleProj K n h m)).map
        (divisorSectionMap (completeBaseMarking_relativeCartier K n h i).1) ≫
      (completePointLineOriginalStageIso K n h m i).hom =
        (modulePullbackUnitIso (originalStageToCompatibleProj K n h m)).hom ≫
          divisorSectionMap (originalStageSingleMarking_relativeCartier K n h m i).1 := by
  let _ := completeCartesianPointIdeal_isIso K n h (baseToSeries K m)
    (originalStageToCompatibleProj K n h m) (family K m n h).hom
    (originalStageToCompatibleProj_isPullback K n h m) i
  exact divisorLinePullbackIsoOfEq_section _ (completeBaseMarking_relativeCartier K n h i).1
    (originalStageSingleMarking_relativeCartier K n h m i).1
    (completeBaseMarking_ker_originalStage K n h m i)

end FLT.Mazur.PolygonInfinitesimalStages
