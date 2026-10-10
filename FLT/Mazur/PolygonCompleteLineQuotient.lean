/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineCover
public import FLT.Mazur.PrincipalSectionExtension
public import FLT.Mazur.IdealAdicLineQuotient
public import FLT.Mazur.IsomorphicClosedPullback
public import FLT.Mazur.PolygonOriginalAdicRealization

/-!
# Complete-base line quotients on the original polygon stages

Any actual complete-base line has its parameter-power quotient identified
with its pullback to the original stage, pushed forward along the original
stage map. The comparison retains the actual adjunction unit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The proper complete-base candidate is Noetherian over its power-series base. -/
instance exactVeroneseProj_isNoetherian : IsNoetherian (exactVeroneseProj K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact Chow.source_isNoetherian (exactVeroneseProjToBase K n h)

variable (L : (exactVeroneseProj K n h).Modules) (hL : LocallyFreeRankOne L)

/-- Restriction of a complete-base line along the actual original stage map. -/
def completeLineOnStage (m : ℕ) : (family K m n h).left.Modules :=
  (pullback (originalStageToCompatibleProj K n h m)).obj L

/-- The parameter-power quotient is the original stage pullback, pushed forward. -/
def completeLineQuotientStageIso (m : ℕ) :
    quotient (compatibleProjAdicIdeal K n h) L (m + 1) ≅
      (pushforward (originalStageToCompatibleProj K n h m)).obj
        (completeLineOnStage K n h L m) :=
  lineQuotientClosedIso _ L hL (m + 1) ≪≫
    IsomorphicClosedPullback.overIso (originalStageAdicIso K n h m)
      (compatibleProjAdicIdeal K n h ^ (m + 1)).subschemeι L
      (originalStageToCompatibleProj K n h m) (originalStageAdicIso_hom_ι K n h m)

/-- The quotient comparison sends projection to the original stage restriction unit. -/
@[reassoc] theorem projection_completeLineQuotientStageIso (m : ℕ) :
    projection (compatibleProjAdicIdeal K n h) L (m + 1) ≫
      (completeLineQuotientStageIso K n h L hL m).hom =
        (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h m)).unit.app L := by
  rw [completeLineQuotientStageIso, Iso.trans_hom, ← Category.assoc,
    projection_lineQuotientClosedIso, IsomorphicClosedPullback.unit_overIso]

/-- All original system transitions compare the actual complete-line restrictions. -/
def completeLineStageTransitionIso {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).obj (completeLineOnStage K n h L b) ≅
      completeLineOnStage K n h L a :=
  (pullbackComp ((stageSystem K n h).map f)
    (originalStageToCompatibleProj K n h b)).app L ≪≫
      (pullbackCongr (originalStageToCompatibleProj_naturality K n h f)).app L

/-- Adic reduction expressed in the original stage pullback modules. -/
def completeLineStageReduction {a b : ℕ} (hab : a ≤ b) :
    (pushforward (originalStageToCompatibleProj K n h b)).obj
        (completeLineOnStage K n h L b) ⟶
      (pushforward (originalStageToCompatibleProj K n h a)).obj
        (completeLineOnStage K n h L a) := by
  let _ := hL.isFinitePresentation
  exact (completeLineQuotientStageIso K n h L hL b).inv ≫
    IdealAdicQuotient.reduction (compatibleProjAdicIdeal K n h) L (Nat.add_le_add_right hab 1) ≫
      (completeLineQuotientStageIso K n h L hL a).hom

/-- The transported reduction preserves the original stage restriction units. -/
@[reassoc] theorem unit_completeLineStageReduction {a b : ℕ} (hab : a ≤ b) :
    (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h b)).unit.app L ≫
      completeLineStageReduction K n h L hL hab =
        (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h a)).unit.app L := by
  let _ := hL.isFinitePresentation
  rw [← projection_completeLineQuotientStageIso K n h L hL b,
    ← projection_completeLineQuotientStageIso K n h L hL a]
  simp only [completeLineStageReduction, Category.assoc, Iso.hom_inv_id_assoc]
  exact IdealAdicQuotient.projection_reduction_assoc (compatibleProjAdicIdeal K n h) L
    (Nat.add_le_add_right hab 1) (completeLineQuotientStageIso K n h L hL a).hom

end FLT.Mazur.PolygonInfinitesimalStages
