/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLineSectionReconstruction
public import FLT.Mazur.AdicOriginalSectionReconstruction

/-!
# Original stage section reconstruction with explicit restriction maps

The original adjunction restrictions and transitions retain their section values.
These typed maps transport formal reconstruction without expanding the complete
Proj construction inside the sheaf pullback definitions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve IdealAdicQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase completeLineStageTransitionIso

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)

include hL

/-- Compatible original pullbacks reconstruct the unique actual complete-line section. -/
theorem completeLineOriginalSection_existsUnique
    (s : ∀ m, Γ(completeLineOnStage A π hne hgen n h L m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (pullbackStageIso (originalStageToCompatibleProj A π hne hgen n h a)
        (originalStageToCompatibleProj A π hne hgen n h b) ((stageSystem A π n h).map (homOfLE hab))
        (originalStageToCompatibleProj_naturality A π hne hgen n h (homOfLE hab)) L).hom.app ⊤
          (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (s b)) = s a) :
    ∃! t : Γ(L, ⊤), ∀ m,
      pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) L t = s m := by
  let _ := hL.isFinitePresentation
  exact existsUnique_section_original (compatibleProjAdicIdeal A π hne hgen n h) L
    (fun m ↦ (family A π m n h).left) (originalStageToCompatibleProj A π hne hgen n h)
    (fun {_ _} hab ↦ (stageSystem A π n h).map (homOfLE hab))
    (fun _ _ hab ↦ originalStageToCompatibleProj_naturality A π hne hgen n h (homOfLE hab))
    (completeLineQuotientStageIso A π hne hgen n h L hL)
    (projection_completeLineQuotientStageIso A π hne hgen n h L hL)
    (completeLineSection_existsUnique A π hne hgen n h L hL) s hs

end FLT.Mazur.PolygonArithmeticStages
