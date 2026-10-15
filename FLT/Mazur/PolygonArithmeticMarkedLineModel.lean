/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteLineCoherence
public import FLT.Mazur.ModulePullbackComparisonTransport
public import FLT.Mazur.PolygonArithmeticLineOriginalReduction

/-!
# Sealed models of the original arithmetic marked lines

The complete and boundary lines keep opaque objects with canonical isomorphisms
to the original divisor lines. Their comparisons retain all original transitions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family
  completeMarkingLine boundaryLine completeMarkingLineStageIso boundaryLineSystemIso

/-- A sealed module object, with no arithmetic instances duplicated in its equality lemma. -/
irreducible_def arithmeticLineModel {X : Scheme} (L : X.Modules) : X.Modules := L

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual complete marked line with its implementation sealed. -/
def completeMarkedLineModel : (exactVeroneseProj A π n h hne hgen).Modules :=
  arithmeticLineModel (completeMarkingLine A π hne hgen n h)

/-- The actual boundary marked line with its implementation sealed. -/
def completeMarkedBoundaryModel (m : ℕ) : (family A π m n h).left.Modules :=
  arithmeticLineModel (boundaryLine A π m n h)

/-- The complete model is the actual complete marked line. -/
def completeMarkedLineModelIso :
    completeMarkedLineModel A π hne hgen n h ≅ completeMarkingLine A π hne hgen n h :=
  eqToIso (arithmeticLineModel_def (completeMarkingLine A π hne hgen n h))

/-- The boundary model is the actual boundary marked line. -/
def completeMarkedBoundaryModelIso (m : ℕ) :
    completeMarkedBoundaryModel A π n h m ≅
      boundaryLine A π m n h :=
  eqToIso (arithmeticLineModel_def (boundaryLine A π m n h))

/-- Every complete marked line remains a line bundle. -/
theorem completeMarkedLineModel_rankOne :
    LocallyFreeRankOne (completeMarkedLineModel A π hne hgen n h) := by
  unfold completeMarkedLineModel
  rw [arithmeticLineModel_def]
  exact (completeMarkingLine_rankOne A π hne hgen n h)

/-- The original complete-to-stage comparison transported to opaque line models. -/
def completeMarkedLineModelStageIso (m : ℕ) :
    (pullback (originalStageToCompatibleProj A π hne hgen n h m)).obj
      (completeMarkedLineModel A π hne hgen n h) ≅
      completeMarkedBoundaryModel A π n h m :=
  (pullback (originalStageToCompatibleProj A π hne hgen n h m)).mapIso
    (completeMarkedLineModelIso A π hne hgen n h) ≪≫
    completeMarkingLineStageIso A π hne hgen n h m ≪≫
      (completeMarkedBoundaryModelIso A π n h m).symm

/-- The original boundary-line transition transported to opaque line models. -/
def completeMarkedLineModelTransition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem A π n h).map f)).obj (completeMarkedBoundaryModel A π n h b) ≅
      completeMarkedBoundaryModel A π n h a :=
  (pullback ((stageSystem A π n h).map f)).mapIso (completeMarkedBoundaryModelIso A π n h b) ≪≫
    boundaryLineSystemIso A π n h f ≪≫
      (completeMarkedBoundaryModelIso A π n h a).symm

/-- All line-model comparisons retain the original commuting stage square. -/
theorem completeMarkedLineModelStageIso_transition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem A π n h).map f)).map
        (completeMarkedLineModelStageIso A π hne hgen n h b).hom ≫
        (completeMarkedLineModelTransition A π n h f).hom =
      (completeLineStageTransitionIso A π hne hgen n h
        (completeMarkedLineModel A π hne hgen n h) f).hom ≫
        (completeMarkedLineModelStageIso A π hne hgen n h a).hom := by
  rw [completeLineStageTransitionIso_eq_sealed]
  apply pullbackComparison_transport
    (originalStageToCompatibleProj A π hne hgen n h a)
    (originalStageToCompatibleProj A π hne hgen n h b)
    ((stageSystem A π n h).map f) (originalStageToCompatibleProj_naturality A π hne hgen n h f)
    (completeMarkedLineModelIso A π hne hgen n h) (completeMarkedBoundaryModelIso A π n h b)
    (completeMarkedBoundaryModelIso A π n h a) (completeMarkingLineStageIso A π hne hgen n h b)
    (boundaryLineSystemIso A π n h f) (completeMarkingLineStageIso A π hne hgen n h a)
  rw [← completeLineStageTransitionIso_eq_sealed]
  exact completeMarkingLineStageIso_transition_hom A π hne hgen n h f

end FLT.Mazur.PolygonArithmeticStages
