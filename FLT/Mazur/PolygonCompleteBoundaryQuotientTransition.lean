/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTransitionCoherence
public import FLT.Mazur.PolygonCompleteCoefficientReconstruction
public import FLT.Mazur.PolygonCompleteLineOriginalReduction

/-!
# Adic quotients with the original boundary transitions

Identify each coefficient quotient with the original boundary power and prove
that quotient reduction is its actual boundary transition after pushforward.
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

/-- The original boundary tensor-power transition pushed to the complete scheme. -/
def completeBoundaryPushforwardTransition {a b : ℕ} (f : a ⟶ b) :
    (pushforward (originalStageToCompatibleProj K n h b)).obj
        (tensorPower (boundaryLine K b n h) (completeCoefficientBoundaryExponent K n h)) ⟶
      (pushforward (originalStageToCompatibleProj K n h a)).obj
        (tensorPower (boundaryLine K a n h) (completeCoefficientBoundaryExponent K n h)) :=
  pushforwardSectionTransition _ _ _ (originalStageToCompatibleProj_naturality K n h f)
    (completeBoundaryPowerStageIso K n h f).hom

/-- The coefficient quotient is the original boundary power, with its actual comparison. -/
def completeCoefficientQuotientBoundaryIso (m : ℕ) :
    IdealAdicQuotient.quotient (compatibleProjAdicIdeal K n h)
        (completeCoefficientLine K n h) (m + 1) ≅
      (pushforward (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h)) :=
  completeCoefficientQuotientStageIso K n h m ≪≫
    (pushforward (originalStageToCompatibleProj K n h m)).mapIso
      (completeCoefficientBoundaryIso K n h m)

/-- The actual quotient projection retains the original boundary comparison. -/
@[reassoc] theorem projection_completeCoefficientQuotientBoundaryIso (m : ℕ) :
    IdealAdicQuotient.projection (compatibleProjAdicIdeal K n h)
        (completeCoefficientLine K n h) (m + 1) ≫
      (completeCoefficientQuotientBoundaryIso K n h m).hom =
      (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h m)).unit.app
        (completeCoefficientLine K n h) ≫
      (pushforward (originalStageToCompatibleProj K n h m)).map
        (completeCoefficientBoundaryIso K n h m).hom := by
  rw [completeCoefficientQuotientBoundaryIso, Iso.trans_hom, Functor.mapIso_hom,
    projection_completeCoefficientQuotientStageIso_assoc]

/-- The adic reductions commute with the ORIGINAL boundary transition maps. -/
@[reassoc] theorem completeCoefficientQuotientBoundaryIso_transition {a b : ℕ}
    (hab : a ≤ b) :
    (completeCoefficientQuotientBoundaryIso K n h b).hom ≫
        completeBoundaryPushforwardTransition K n h (homOfLE hab) =
      IdealAdicQuotient.reduction (compatibleProjAdicIdeal K n h) (completeCoefficientLine K n h)
          (Nat.add_le_add_right hab 1) ≫
        (completeCoefficientQuotientBoundaryIso K n h a).hom := by
  have hs := pushforwardSectionTransition_square
    (originalStageToCompatibleProj K n h a) (originalStageToCompatibleProj K n h b)
    ((stageSystem K n h).map (homOfLE hab))
    (originalStageToCompatibleProj_naturality K n h (homOfLE hab))
    (completeCoefficientBoundaryIso K n h b).hom
    (completeCoefficientBoundaryIso K n h a).hom
    (completeBoundaryPowerStageIso K n h (homOfLE hab)).hom
    (completeLineStageTransitionIso K n h (completeCoefficientLine K n h) (homOfLE hab)).hom
    (completeCoefficientBoundaryIso_transition K n h (homOfLE hab))
  simp only [completeCoefficientQuotientBoundaryIso, Iso.trans_hom, Functor.mapIso_hom,
    completeBoundaryPushforwardTransition, Category.assoc]
  rw [hs]
  exact completeLineQuotientStageIso_original_transition_assoc K n h _
    (completeCoefficientLine_rankOne K n h) hab _

end FLT.Mazur.PolygonInfinitesimalStages
