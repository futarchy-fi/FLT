/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteLineSectionReconstruction
public import FLT.Mazur.AdicOriginalSectionReconstruction

/-!
# Original stage section reconstruction with explicit restriction maps

The original adjunction restrictions and transitions retain their section values.
These typed maps transport formal reconstruction without expanding the complete
Proj construction inside the sheaf pullback definitions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve IdealAdicQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase completeLineStageTransitionIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj K n h).Modules) (hL : LocallyFreeRankOne L)

include hL

/-- Compatible original pullbacks reconstruct the unique actual complete-line section. -/
theorem completeLineOriginalSection_existsUnique
    (s : ∀ m, Γ(completeLineOnStage K n h L m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (pullbackStageIso (originalStageToCompatibleProj K n h a)
        (originalStageToCompatibleProj K n h b) ((stageSystem K n h).map (homOfLE hab))
        (originalStageToCompatibleProj_naturality K n h (homOfLE hab)) L).hom.app ⊤
          (pullGlobal ((stageSystem K n h).map (homOfLE hab)) _ (s b)) = s a) :
    ∃! t : Γ(L, ⊤), ∀ m, pullGlobal (originalStageToCompatibleProj K n h m) L t = s m := by
  let _ := hL.isFinitePresentation
  exact existsUnique_section_original (compatibleProjAdicIdeal K n h) L
    (fun m ↦ (family K m n h).left) (originalStageToCompatibleProj K n h)
    (fun {_ _} hab ↦ (stageSystem K n h).map (homOfLE hab))
    (fun _ _ hab ↦ originalStageToCompatibleProj_naturality K n h (homOfLE hab))
    (completeLineQuotientStageIso K n h L hL)
    (projection_completeLineQuotientStageIso K n h L hL)
    (completeLineSection_existsUnique K n h L hL) s hs

end FLT.Mazur.PolygonInfinitesimalStages
