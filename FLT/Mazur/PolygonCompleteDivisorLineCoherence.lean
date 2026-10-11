/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullbackTransport
public import FLT.Mazur.PolygonCompleteDivisorLine
public import FLT.Mazur.PolygonCompleteLineQuotient

/-!
# Original transition coherence of the complete marked line

The canonical complete-to-stage comparisons commute with the original boundary
line transitions, including the specified equality of the composite scheme map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family boundaryLine

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual marking-line comparisons respect every original stage transition. -/
theorem completeMarkingLineStageIso_transition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).mapIso (completeMarkingLineStageIso K n h b) ≪≫
        boundaryLineSystemIso K n h f =
      completeLineStageTransitionIso K n h (completeMarkingLine K n h) f ≪≫
        completeMarkingLineStageIso K n h a := by
  let _ := boundaryIdeal_systemMap_isIso K n h f
  simpa only [completeLineStageTransitionIso, Iso.trans_assoc, completeMarkingLineStageIso,
    boundaryLineSystemIso, completeMarkingLine, boundaryLine] using
    (divisorLinePullbackIsoOfEq_comp_eq
    (I := completeMarkingDivisor K n h)
    (J := boundaryIdeal K b n h) (K := boundaryIdeal K a n h) _ _ _
    (originalStageToCompatibleProj_naturality K n h f).symm
    (completeMarkingDivisor_relativeCartier K n h).1
    (boundaryIdeal_cartier K b n h).1 (boundaryIdeal_cartier K a n h).1
    (completeMarkingDivisor_originalBoundary K n h b)
    (boundaryIdeal_systemMap K n h f) (completeMarkingDivisor_originalBoundary K n h a))

/-- The same coherence as equality of actual sheaf morphisms. -/
@[reassoc] theorem completeMarkingLineStageIso_transition_hom {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).map (completeMarkingLineStageIso K n h b).hom ≫
        (boundaryLineSystemIso K n h f).hom =
      (completeLineStageTransitionIso K n h (completeMarkingLine K n h) f).hom ≫
        (completeMarkingLineStageIso K n h a).hom :=
  congrArg Iso.hom (completeMarkingLineStageIso_transition K n h f)

end FLT.Mazur.PolygonInfinitesimalStages
