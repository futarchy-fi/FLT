/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStagePoleSections
public import FLT.Mazur.DivisorComparedSectionStep

/-!
# The canonical divisor factor of the original stage X section

Prove transport of a pole step in variable degree before specializing to
degree two. This avoids expanding the large concrete degree-three tensor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  family originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
  completePointLineOriginalStageIso completePointPowerOriginalStageIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "P" => completePointLine K n h i
local notation "Q" => originalStageSinglePointLine K n h m i
local notation "hP" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "hQ" => And.left (originalStageSingleMarking_relativeCartier K n h m i)

/-- Transport of the original pole filtration preserves its literal canonical section factor. -/
theorem completePointPowerStageSection_cons (d : ℕ) (t : Γ(tensorPower (P) d, ⊤)) :
    completePointPowerStageSection K n h m i (d + 1)
        (SectionGradedMultiplication.cons (P) d ⊤ (divisorSection hP ⊤) t) =
      SectionGradedMultiplication.cons (Q) d ⊤ (divisorSection hQ ⊤)
        (completePointPowerStageSection K n h m i d t) := by
  have he : DivisorLineSectionCompatible (originalStageToCompatibleProj K n h m)
      hP hQ (completePointLineOriginalStageIso K n h m i) :=
    completePointLineOriginalStageIso_section K n h m i
  simpa only [completePointPowerStageSection, completePointPowerOriginalStageIso,
    completePointLine, originalStageSinglePointLine] using
    he.tensorPower_cons d t


/-- The original stage X section retains exactly the canonical divisor times its chosen lift. -/
theorem completePointStageProjectiveSections_X :
    completePointStageProjectiveSections K n h m i 0 =
      SectionGradedMultiplication.cons (Q) 2 ⊤ (divisorSection hQ ⊤)
        (completePointStagePoleTwo K n h m i) := by
  change completePointPowerStageSection K n h m i 3
    (completePointProjectiveX K n h i) = _
  rw [completePointProjectiveX_canonicalFactor]
  exact completePointPowerStageSection_cons K n h m i 2 _

end FLT.Mazur.PolygonInfinitesimalStages
