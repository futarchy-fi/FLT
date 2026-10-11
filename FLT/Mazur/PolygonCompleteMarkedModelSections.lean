/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedLineModel
public import FLT.Mazur.PolygonCompleteComparedSectionReconstruction

/-!
# Reconstructing the complete marked line from original boundary sections

The original adjunction restrictions and transitions transport formal section
reconstruction to the actual original boundary lines.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] boundaryLine family originalStageToCompatibleProj
  completeMarkingLine
  exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Actual original-stage compatibility reconstructs a unique complete marked section. -/
theorem completeMarkedModelSection_existsUnique
    (s : ∀ m, Γ(completeMarkedBoundaryModel K n h m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (completeMarkedModelTransition K n h (homOfLE hab)).hom.app ⊤
        (pullGlobal ((stageSystem K n h).map (homOfLE hab))
          (completeMarkedBoundaryModel K n h b) (s b)) = s a) :
    ∃! t : Γ(completeMarkedLineModel K n h, ⊤), ∀ m,
      (completeMarkedModelStageIso K n h m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj K n h m)
          (completeMarkedLineModel K n h) t) = s m := by
  exact completeLineComparedSection_existsUnique K n h (completeMarkedLineModel K n h)
    (completeMarkedLineModel_rankOne K n h) (fun m ↦ completeMarkedBoundaryModel K n h m)
    (completeMarkedModelStageIso K n h)
    (fun {_ _} f ↦ (completeMarkedModelTransition K n h f).hom)
    (fun {_ _} f ↦ completeMarkedModelStageIso_transition K n h f) s hs

end FLT.Mazur.PolygonInfinitesimalStages
