/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteDivisorLineCoherence

/-!
# Sealed original comparisons for the complete marked line

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

/-- The exact original marked-line comparison, with a sealed implementation. -/
irreducible_def completeMarkedStageComparison (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj (completeMarkingLine K n h) ≅
      boundaryLine K m n h :=
  completeMarkingLineStageIso K n h m

/-- The exact original boundary transition, with a sealed implementation. -/
irreducible_def completeMarkedBoundaryTransition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).obj (boundaryLine K b n h) ≅
      boundaryLine K a n h :=
  boundaryLineSystemIso K n h f

/-- The sealed comparisons retain the original commuting transition square. -/
theorem completeMarkedStageComparison_transition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).map (completeMarkedStageComparison K n h b).hom ≫
        (completeMarkedBoundaryTransition K n h f).hom =
      (completeLineStageTransitionIso K n h (completeMarkingLine K n h) f).hom ≫
        (completeMarkedStageComparison K n h a).hom := by
  rw [completeMarkedStageComparison_def, completeMarkedStageComparison_def,
    completeMarkedBoundaryTransition_def]
  exact completeMarkingLineStageIso_transition_hom K n h f

end FLT.Mazur.PolygonInfinitesimalStages
