/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DivisorLinePullbackTransport
public import FLT.Mazur.PolygonArithmeticCompleteDivisorLine
public import FLT.Mazur.PolygonArithmeticCompleteLineQuotient

/-!
# Original transition coherence of the complete marked line

The canonical complete-to-stage comparisons commute with the original boundary
line transitions, including the specified equality of the composite scheme map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family boundaryLine

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual marking-line comparisons respect every original stage transition. -/
theorem completeMarkingLineStageIso_transition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem A π n h).map f)).mapIso
      (completeMarkingLineStageIso A π hne hgen n h b) ≪≫
        boundaryLineSystemIso A π n h f =
      completeLineStageTransitionIso A π hne hgen n h (completeMarkingLine A π hne hgen n h) f ≪≫
        completeMarkingLineStageIso A π hne hgen n h a := by
  let _ := boundaryIdeal_systemMap_isIso A π n h f
  simpa only [completeLineStageTransitionIso, Iso.trans_assoc, completeMarkingLineStageIso,
    boundaryLineSystemIso, completeMarkingLine, boundaryLine] using
    (divisorLinePullbackIsoOfEq_comp_eq
    (I := completeMarkingDivisor A π hne hgen n h)
    (J := boundaryIdeal A π b n h) (K := boundaryIdeal A π a n h) _ _ _
    (originalStageToCompatibleProj_naturality A π hne hgen n h f).symm
    (completeMarkingDivisor_relativeCartier A π hne hgen n h).1
    (boundaryIdeal_cartier A π b n h).1 (boundaryIdeal_cartier A π a n h).1
    (completeMarkingDivisor_originalBoundary A π hne hgen n h b)
    (boundaryIdeal_systemMap A π n h f)
      (completeMarkingDivisor_originalBoundary A π hne hgen n h a))

/-- The same coherence as equality of actual sheaf morphisms. -/
@[reassoc] theorem completeMarkingLineStageIso_transition_hom {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem A π n h).map f)).map
      (completeMarkingLineStageIso A π hne hgen n h b).hom ≫
        (boundaryLineSystemIso A π n h f).hom =
      (completeLineStageTransitionIso A π hne hgen n h
        (completeMarkingLine A π hne hgen n h) f).hom ≫
        (completeMarkingLineStageIso A π hne hgen n h a).hom :=
  congrArg Iso.hom (completeMarkingLineStageIso_transition A π hne hgen n h f)

end FLT.Mazur.PolygonArithmeticStages
