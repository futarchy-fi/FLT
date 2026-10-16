/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStageLineComparison
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Original pole powers at every full infinitesimal stage

Tensoring the actual single-marking comparison preserves its canonical section
in every degree. In particular, the degree-two and degree-three comparisons
retain the original finite-stage marking and its nilpotents.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  family originalStageToCompatibleProj ModuleSheafTensor.tensor
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)

/-- The original complete pole power compared with the same finite-stage divisor power. -/
def completePointPowerOriginalStageIso (d : ℕ) :
    (Scheme.Modules.pullback (originalStageToCompatibleProj K n h m)).obj
      (tensorPower (completePointLine K n h i) d) ≅
        tensorPower (originalStageSinglePointLine K n h m i) d :=
  tensorPowerPullbackComparison (originalStageToCompatibleProj K n h m)
    (completePointLineOriginalStageIso K n h m i) d

/-- The stage power comparison preserves the literal canonical divisor power. -/
theorem completePointPowerOriginalStageIso_section (d : ℕ) :
    (completePointPowerOriginalStageIso K n h m i d).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj K n h m) _
          (tensorPowerSection _ ⊤
            (divisorSection (completeBaseMarking_relativeCartier K n h i).1 ⊤) d)) =
      tensorPowerSection _ ⊤
        (divisorSection (originalStageSingleMarking_relativeCartier K n h m i).1 ⊤) d := by
  have he : DivisorLineSectionCompatible (originalStageToCompatibleProj K n h m)
      (completeBaseMarking_relativeCartier K n h i).1
      (originalStageSingleMarking_relativeCartier K n h m i).1
      (completePointLineOriginalStageIso K n h m i) :=
    completePointLineOriginalStageIso_section K n h m i
  exact he.tensorPower_section d

/-- Transport an actual chosen complete section, without choosing a new stage lift. -/
def completePointPowerStageSection (d : ℕ)
    (s : Γ(tensorPower (completePointLine K n h i) d, ⊤)) :
    Γ(tensorPower (originalStageSinglePointLine K n h m i) d, ⊤) :=
  (completePointPowerOriginalStageIso K n h m i d).hom.app ⊤
    (pullGlobal (originalStageToCompatibleProj K n h m) _ s)

/-- Transport retains the actual coefficient map on scalars. -/
theorem completePointPowerStageSection_smul (d : ℕ)
    (a : Γ(exactVeroneseProj K n h, ⊤))
    (s : Γ(tensorPower (completePointLine K n h i) d, ⊤)) :
    completePointPowerStageSection K n h m i d (a • s) =
      (originalStageToCompatibleProj K n h m).appTop a •
        completePointPowerStageSection K n h m i d s := by
  simp only [completePointPowerStageSection, map_smulₛₗ, Hom.app_smul]

end FLT.Mazur.PolygonInfinitesimalStages
