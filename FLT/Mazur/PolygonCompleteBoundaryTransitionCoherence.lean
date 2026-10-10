/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientCoherence
public import FLT.Mazur.PolygonCompleteBoundaryCoordinateTransport
public import FLT.Mazur.PolygonCompleteBoundarySectionTransport
public import FLT.Mazur.PolygonCompleteLineQuotient

/-!
# Original stage coherence of the complete boundary comparison

The constructed coefficient-line comparisons intertwine the actual original
boundary tensor-power transition maps on all infinitesimal stages.
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

/-- The complete boundary comparisons commute with the ORIGINAL boundary stage maps. -/
theorem completeCoefficientBoundaryIso_transition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).map (completeCoefficientBoundaryIso K n h b).hom ≫
        (completeBoundaryPowerStageIso K n h f).hom =
      (completeLineStageTransitionIso K n h (completeCoefficientLine K n h) f).hom ≫
        (completeCoefficientBoundaryIso K n h a).hom := by
  apply completeCoefficientSection_comparison_coherence K n h f
  intro i
  exact (congrArg (fun s ↦ (completeBoundaryPowerStageIso K n h f).hom.app ⊤
    (pullGlobal ((stageSystem K n h).map f) _ s))
    (completeCoefficientBoundaryIso_section K n h b i)).trans
      ((completeBoundaryPowerStageIso_section K n h f i).trans
        (completeCoefficientBoundaryIso_section K n h a i).symm)

end FLT.Mazur.PolygonInfinitesimalStages
