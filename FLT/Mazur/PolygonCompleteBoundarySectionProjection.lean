/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryQuotientTransition

/-!
# Original boundary restriction as an actual section morphism

Keep the original adjunction section map typed before evaluating global sections.
The adic projection factors through precisely this original boundary restriction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  originalStageToCompatibleProj completeCoefficientBoundaryIso ModuleSheafTensor.tensor
  completeBoundaryPowerStageIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual original boundary restriction, through the original adjunction unit. -/
@[irreducible] def completeBoundaryRestriction (m : ℕ) :
    completeCoefficientLine K n h ⟶
      (pushforward (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h)) :=
  moduleSectionTransport (originalStageToCompatibleProj K n h m)
    (completeCoefficientBoundaryIso K n h m).hom

/-- The quotient projection is the original boundary restriction under the actual comparison. -/
@[reassoc] theorem projection_completeBoundaryRestriction (m : ℕ) :
    IdealAdicQuotient.projection (compatibleProjAdicIdeal K n h)
        (completeCoefficientLine K n h) (m + 1) ≫
      (completeCoefficientQuotientBoundaryIso K n h m).hom =
        completeBoundaryRestriction K n h m := by
  unfold completeBoundaryRestriction moduleSectionTransport
  exact projection_completeCoefficientQuotientBoundaryIso K n h m

/-- Global boundary restriction is the original pullback and boundary comparison. -/
theorem completeBoundaryRestriction_top (m : ℕ) (t : Γ(completeCoefficientLine K n h, ⊤)) :
    (completeBoundaryRestriction K n h m).app ⊤ t =
      (completeCoefficientBoundaryIso K n h m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj K n h m)
          (completeCoefficientLine K n h) t) := by
  rw [completeBoundaryRestriction]
  exact moduleSectionTransport_top _ _ t

/-- The original boundary transition retains actual section pullback on global sections. -/
theorem completeBoundaryPushforwardTransition_top {a b : ℕ} (f : a ⟶ b)
    (s : Γ(tensorPower (boundaryLine K b n h)
      (completeCoefficientBoundaryExponent K n h), ⊤)) :
    (completeBoundaryPushforwardTransition K n h f).app ⊤ s =
      (completeBoundaryPowerStageIso K n h f).hom.app ⊤
        (pullGlobal ((stageSystem K n h).map f) _ s) :=
  pushforwardSectionTransition_top _ _ _ _ _ s

end FLT.Mazur.PolygonInfinitesimalStages
