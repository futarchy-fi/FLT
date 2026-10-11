/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteDivisorRestriction
public import FLT.Mazur.PolygonInfinitesimalStageLine

/-!
# The complete marked line and its original stage restrictions

Dualizing the actual complete marking ideal gives a coherent line. Its canonical
pullback comparison identifies every original stage with the original boundary
line and preserves the actual divisor section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The positive line of the actual complete marked divisor. -/
def completeMarkingLine : (exactVeroneseProj K n h).Modules :=
  divisorLineBundle (completeMarkingDivisor K n h)
    (completeMarkingDivisor_relativeCartier K n h).1

/-- The complete marked line is locally free of rank one. -/
theorem completeMarkingLine_rankOne : LocallyFreeRankOne (completeMarkingLine K n h) :=
  (completeMarkingDivisor_relativeCartier K n h).1.divisorLineBundle_locallyFreeRankOne

/-- The complete marked line is coherent. -/
theorem completeMarkingLine_isFinitePresentation :
    (completeMarkingLine K n h).IsFinitePresentation :=
  (completeMarkingLine_rankOne K n h).isFinitePresentation

/-- The canonical ideal comparison is invertible at every original stage. -/
instance completeMarkingIdeal_stage_isIso (m : ℕ) :
    IsIso (idealModulePullbackHom (completeMarkingDivisor K n h)
      (originalStageToCompatibleProj K n h m)) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (completeMarkingDivisor_relativeCartier K n h).1
  rw [completeMarkingDivisor_originalBoundary]
  exact (boundaryIdeal_cartier K m n h).1

/-- The complete marking line restricts canonically to the original boundary line. -/
def completeMarkingLineStageIso (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj (completeMarkingLine K n h) ≅
      boundaryLine K m n h :=
  divisorLinePullbackIsoOfEq _ (completeMarkingDivisor_relativeCartier K n h).1
    (boundaryIdeal_cartier K m n h).1 (completeMarkingDivisor_originalBoundary K n h m)

/-- The comparison retains the actual canonical divisor section. -/
@[reassoc] theorem completeMarkingLineStageIso_section (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).map
        (divisorSectionMap (completeMarkingDivisor_relativeCartier K n h).1) ≫
      (completeMarkingLineStageIso K n h m).hom =
        (modulePullbackUnitIso (originalStageToCompatibleProj K n h m)).hom ≫
          divisorSectionMap (boundaryIdeal_cartier K m n h).1 :=
  divisorLinePullbackIsoOfEq_section _ (completeMarkingDivisor_relativeCartier K n h).1
    (boundaryIdeal_cartier K m n h).1 (completeMarkingDivisor_originalBoundary K n h m)

end FLT.Mazur.PolygonInfinitesimalStages
