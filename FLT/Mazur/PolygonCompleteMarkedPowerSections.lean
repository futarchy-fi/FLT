/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedPowerModel
public import FLT.Mazur.PolygonCompleteComparedSectionReconstruction

/-!
# Reconstructing sections of every actual complete marked power

Compatible sections of the original boundary power models reconstruct a unique
section of the complete marked power model. The comparisons and transitions
are transported from the original marked powers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family originalStageToCompatibleProj
  exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Compatible original boundary-power sections determine a unique complete power section. -/
theorem completeMarkedPowerModelSection_existsUnique (d : ℕ)
    (s : ∀ m, Γ(completeMarkedBoundaryPowerModel K n h d m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (completeMarkedPowerModelTransition K n h d (homOfLE hab)).hom.app ⊤
        (pullGlobal ((stageSystem K n h).map (homOfLE hab))
          (completeMarkedBoundaryPowerModel K n h d b) (s b)) = s a) :
    ∃! t : Γ(completeMarkedPowerModel K n h d, ⊤), ∀ m,
      (completeMarkedPowerModelStageIso K n h d m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj K n h m)
          (completeMarkedPowerModel K n h d) t) = s m := by
  exact completeLineComparedSection_existsUnique K n h (completeMarkedPowerModel K n h d)
    (completeMarkedPowerModel_rankOne K n h d)
    (fun m ↦ completeMarkedBoundaryPowerModel K n h d m)
    (completeMarkedPowerModelStageIso K n h d)
    (fun {_ _} f ↦ (completeMarkedPowerModelTransition K n h d f).hom)
    (fun {_ _} f ↦ completeMarkedPowerModelStageIso_transition K n h d f) s hs

end FLT.Mazur.PolygonInfinitesimalStages
