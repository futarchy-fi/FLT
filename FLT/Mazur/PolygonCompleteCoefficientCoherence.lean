/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientStageCoherence
public import FLT.Mazur.PolygonCompleteBoundaryCoordinateTransport
public import FLT.Mazur.PolygonCompleteLineQuotient

/-!
# Coordinates detect complete coefficient comparison squares

Specialize coordinate detection before substituting the original boundary modules.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  originalStageToCompatibleProj completeCoefficientBoundaryIso ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The sealed comparison is exactly the original complete-line stage isomorphism. -/
theorem completeLineStageTransitionIso_eq_sealed
    (L : (exactVeroneseProj K n h).Modules) {a b : ℕ} (f : a ⟶ b) :
    completeLineStageTransitionIso K n h L f =
      pullbackStageIso (originalStageToCompatibleProj K n h a)
        (originalStageToCompatibleProj K n h b) ((stageSystem K n h).map f)
        (originalStageToCompatibleProj_naturality K n h f) L :=
  (pullbackStageIso_def _ _ _ _ L).symm

/-- Original complete coordinates detect the comparison square on any stage modules. -/
theorem completeCoefficientSection_comparison_coherence {a b : ℕ} (f : a ⟶ b)
    {M : (family K a n h).left.Modules} {N : (family K b n h).left.Modules}
    (u : completeLineOnStage K n h (completeCoefficientLine K n h) a ⟶ M)
    (v : completeLineOnStage K n h (completeCoefficientLine K n h) b ⟶ N)
    (w : (pullback ((stageSystem K n h).map f)).obj N ⟶ M)
    (hs : ∀ i, w.app ⊤ (pullGlobal ((stageSystem K n h).map f) N
        (v.app ⊤ (pullGlobal (originalStageToCompatibleProj K n h b)
          (completeCoefficientLine K n h) (completeCoefficientSection K n h i)))) =
      u.app ⊤ (pullGlobal (originalStageToCompatibleProj K n h a)
        (completeCoefficientLine K n h) (completeCoefficientSection K n h i))) :
    (pullback ((stageSystem K n h).map f)).map v ≫ w =
      (completeLineStageTransitionIso K n h (completeCoefficientLine K n h) f).hom ≫ u := by
  rw [completeLineStageTransitionIso_eq_sealed]
  exact GradedProjLine.coefficientSection_stage_coherence
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
    (completeCoefficientCoordinates K n h).coordinate
    (completeCoefficientCoordinates K n h).homogeneous
    (originalStageToCompatibleProj K n h a) (originalStageToCompatibleProj K n h b)
    ((stageSystem K n h).map f) (originalStageToCompatibleProj_naturality K n h f)
    (completeCoefficientCoordinates K n h).covers u v w hs

end FLT.Mazur.PolygonInfinitesimalStages
