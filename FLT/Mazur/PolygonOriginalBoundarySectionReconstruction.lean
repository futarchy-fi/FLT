/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundarySectionProjection
public import FLT.Mazur.AdicSectionIsoReconstruction

/-!
# Reconstruction from original boundary sections

Sections compatible with the original boundary tensor-power transitions
come from a unique section of the actual complete coefficient line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  originalStageToCompatibleProj completeCoefficientBoundaryIso ModuleSheafTensor.tensor
  completeBoundaryPowerStageIso

attribute [local instance] completeCoefficientLine_isFinitePresentation

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Actual original-stage compatibility reconstructs a unique complete coefficient section. -/
theorem originalBoundarySection_existsUnique
    (s : ∀ m, Γ(tensorPower (boundaryLine K m n h)
      (completeCoefficientBoundaryExponent K n h), ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (completeBoundaryPowerStageIso K n h (homOfLE hab)).hom.app ⊤
        (pullGlobal ((stageSystem K n h).map (homOfLE hab)) _ (s b)) = s a) :
    ∃! t : Γ(completeCoefficientLine K n h, ⊤), ∀ m,
      (completeCoefficientBoundaryIso K n h m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj K n h m)
          (completeCoefficientLine K n h) t) = s m := by
  have hr := existsUnique_section_of_quotient_iso
    (compatibleProjAdicIdeal K n h) (completeCoefficientLine K n h)
    (fun m ↦ (pushforward (originalStageToCompatibleProj K n h m)).obj
      (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h)))
    (completeCoefficientQuotientBoundaryIso K n h)
    (completeBoundaryRestriction K n h) (projection_completeBoundaryRestriction K n h)
    (fun {_ _} hab ↦ completeBoundaryPushforwardTransition K n h (homOfLE hab))
    (fun _ _ hab ↦ completeCoefficientQuotientBoundaryIso_transition K n h hab)
    (completeCoefficientSection_existsUnique K n h) s
    (fun a b hab ↦ (completeBoundaryPushforwardTransition_top K n h (homOfLE hab)
      (s b)).trans (hs a b hab))
  simpa only [completeBoundaryRestriction_top] using hr

end FLT.Mazur.PolygonInfinitesimalStages
