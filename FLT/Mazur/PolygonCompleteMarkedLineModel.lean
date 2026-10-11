/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedStageComparison
public import FLT.Mazur.ModulePullbackComparisonTransport
public import FLT.Mazur.PolygonCompleteCoefficientCoherence

/-!
# Opaque line objects for complete marked section reconstruction

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
  originalStageToCompatibleProj family boundaryLine completeMarkingLine
  completeMarkingLineStageIso boundaryLineSystemIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- An opaque model of the actual complete marked line. -/
irreducible_def completeMarkedLineModel : (exactVeroneseProj K n h).Modules :=
  completeMarkingLine K n h

/-- An opaque model of each actual original boundary line. -/
irreducible_def completeMarkedBoundaryModel (m : ℕ) : (family K m n h).left.Modules :=
  boundaryLine K m n h

/-- The complete opaque model is canonically the actual marked line. -/
def completeMarkedLineModelIso : completeMarkedLineModel K n h ≅ completeMarkingLine K n h :=
  eqToIso (completeMarkedLineModel_def K n h)

/-- Every opaque boundary model is canonically the original boundary line. -/
def completeMarkedBoundaryModelIso (m : ℕ) :
    completeMarkedBoundaryModel K n h m ≅ boundaryLine K m n h :=
  eqToIso (completeMarkedBoundaryModel_def K n h m)

/-- The opaque complete model remains a genuine line bundle. -/
theorem completeMarkedLineModel_rankOne : LocallyFreeRankOne (completeMarkedLineModel K n h) := by
  rw [completeMarkedLineModel_def]
  exact completeMarkingLine_rankOne K n h

/-- Actual stage comparison between opaque models, retaining both canonical identifications. -/
def completeMarkedModelStageIso (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj (completeMarkedLineModel K n h) ≅
      completeMarkedBoundaryModel K n h m :=
  (pullback (originalStageToCompatibleProj K n h m)).mapIso (completeMarkedLineModelIso K n h) ≪≫
    completeMarkedStageComparison K n h m ≪≫ (completeMarkedBoundaryModelIso K n h m).symm

/-- Actual boundary transition between opaque models. -/
def completeMarkedModelTransition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).obj (completeMarkedBoundaryModel K n h b) ≅
      completeMarkedBoundaryModel K n h a :=
  (pullback ((stageSystem K n h).map f)).mapIso (completeMarkedBoundaryModelIso K n h b) ≪≫
    completeMarkedBoundaryTransition K n h f ≪≫ (completeMarkedBoundaryModelIso K n h a).symm

/-- Model comparisons retain the original commuting transition square. -/
theorem completeMarkedModelStageIso_transition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).map (completeMarkedModelStageIso K n h b).hom ≫
        (completeMarkedModelTransition K n h f).hom =
      (completeLineStageTransitionIso K n h (completeMarkedLineModel K n h) f).hom ≫
        (completeMarkedModelStageIso K n h a).hom := by
  rw [completeLineStageTransitionIso_eq_sealed]
  apply pullbackComparison_transport
    (originalStageToCompatibleProj K n h a) (originalStageToCompatibleProj K n h b)
    ((stageSystem K n h).map f) (originalStageToCompatibleProj_naturality K n h f)
    (completeMarkedLineModelIso K n h) (completeMarkedBoundaryModelIso K n h b)
    (completeMarkedBoundaryModelIso K n h a) (completeMarkedStageComparison K n h b)
    (completeMarkedBoundaryTransition K n h f) (completeMarkedStageComparison K n h a)
  rw [← completeLineStageTransitionIso_eq_sealed]
  exact completeMarkedStageComparison_transition K n h f

end FLT.Mazur.PolygonInfinitesimalStages
