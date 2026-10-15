/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteLineQuotient
public import FLT.Mazur.ModulePushforwardTransitionCoherence

/-!
# Original stage transitions and complete-line quotient reduction

The actual adjunction transition equals the transported adic reduction.
This is proved from the common original projection, which is epimorphic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve IdealAdicQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) [L.IsFinitePresentation]
  (hL : LocallyFreeRankOne L)

omit [L.IsFinitePresentation] [IsAdicComplete (ideal A π) A] in
/-- The original complete-line transition is the sealed pullback comparison. -/
theorem completeLineStageTransitionIso_eq_sealed {a b : ℕ} (f : a ⟶ b) :
    completeLineStageTransitionIso A π hne hgen n h L f =
      pullbackStageIso (originalStageToCompatibleProj A π hne hgen n h a)
        (originalStageToCompatibleProj A π hne hgen n h b) ((stageSystem A π n h).map f)
        (originalStageToCompatibleProj_naturality A π hne hgen n h f) L :=
  (pullbackStageIso_def _ _ _ _ L).symm

/-- Quotient reduction agrees with the transition of the original stage restrictions. -/
@[reassoc] theorem completeLineQuotientStageIso_original_transition {a b : ℕ}
    (hab : a ≤ b) :
    (completeLineQuotientStageIso A π hne hgen n h L hL b).hom ≫
      pushforwardSectionTransition (originalStageToCompatibleProj A π hne hgen n h a)
        (originalStageToCompatibleProj A π hne hgen n h b) ((stageSystem A π n h).map (homOfLE hab))
        (originalStageToCompatibleProj_naturality A π hne hgen n h (homOfLE hab))
        (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom =
      IdealAdicQuotient.reduction (compatibleProjAdicIdeal A π hne hgen n h) L
        (Nat.add_le_add_right hab 1) ≫
        (completeLineQuotientStageIso A π hne hgen n h L hL a).hom := by
  apply (cancel_epi (IdealAdicQuotient.projection
    (compatibleProjAdicIdeal A π hne hgen n h) L (b + 1))).mp
  rw [← Category.assoc, projection_completeLineQuotientStageIso,
    ← Category.assoc, projection_reduction, projection_completeLineQuotientStageIso]
  rw [completeLineStageTransitionIso_eq_sealed]
  exact unit_pushforwardSectionTransition _ _ _ _ L

/-- The transported reduction is the original direct-image stage transition. -/
theorem completeLineStageReduction_eq_original {a b : ℕ} (hab : a ≤ b) :
    completeLineStageReduction A π hne hgen n h L hL hab =
      pushforwardSectionTransition (originalStageToCompatibleProj A π hne hgen n h a)
        (originalStageToCompatibleProj A π hne hgen n h b) ((stageSystem A π n h).map (homOfLE hab))
        (originalStageToCompatibleProj_naturality A π hne hgen n h (homOfLE hab))
        (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom := by
  dsimp only [completeLineStageReduction]
  rw [← completeLineQuotientStageIso_original_transition A π hne hgen n h L hL hab,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonArithmeticStages
