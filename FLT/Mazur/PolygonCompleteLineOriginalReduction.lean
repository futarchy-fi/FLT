/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientCoherence
public import FLT.Mazur.ModulePushforwardTransitionCoherence

/-!
# Original stage transitions and complete-line quotient reduction

The actual adjunction transition equals the transported adic reduction.
This is proved from the common original projection, which is epimorphic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve IdealAdicQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj K n h).Modules) [L.IsFinitePresentation]
  (hL : LocallyFreeRankOne L)

/-- Quotient reduction agrees with the transition of the original stage restrictions. -/
@[reassoc] theorem completeLineQuotientStageIso_original_transition {a b : ℕ}
    (hab : a ≤ b) :
    (completeLineQuotientStageIso K n h L hL b).hom ≫
      pushforwardSectionTransition (originalStageToCompatibleProj K n h a)
        (originalStageToCompatibleProj K n h b) ((stageSystem K n h).map (homOfLE hab))
        (originalStageToCompatibleProj_naturality K n h (homOfLE hab))
        (completeLineStageTransitionIso K n h L (homOfLE hab)).hom =
      IdealAdicQuotient.reduction (compatibleProjAdicIdeal K n h) L (Nat.add_le_add_right hab 1) ≫
        (completeLineQuotientStageIso K n h L hL a).hom := by
  apply (cancel_epi (IdealAdicQuotient.projection (compatibleProjAdicIdeal K n h) L (b + 1))).mp
  rw [← Category.assoc, projection_completeLineQuotientStageIso,
    ← Category.assoc, projection_reduction, projection_completeLineQuotientStageIso]
  rw [completeLineStageTransitionIso_eq_sealed]
  exact unit_pushforwardSectionTransition _ _ _ _ L

/-- The transported reduction is the original direct-image stage transition. -/
theorem completeLineStageReduction_eq_original {a b : ℕ} (hab : a ≤ b) :
    completeLineStageReduction K n h L hL hab =
      pushforwardSectionTransition (originalStageToCompatibleProj K n h a)
        (originalStageToCompatibleProj K n h b) ((stageSystem K n h).map (homOfLE hab))
        (originalStageToCompatibleProj_naturality K n h (homOfLE hab))
        (completeLineStageTransitionIso K n h L (homOfLE hab)).hom := by
  dsimp only [completeLineStageReduction]
  rw [← completeLineQuotientStageIso_original_transition K n h L hL hab,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
