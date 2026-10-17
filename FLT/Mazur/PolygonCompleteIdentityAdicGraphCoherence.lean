/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicGraphSections

/-!
# The original adic graph sections form a compatible system

The literal base-changed graphs have actual adjacent restriction maps.
Their source and target coordinates commute with the original restrictions,
and the constructed whole-input sections commute with these graph maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h
local notation "r" => completeIdentityActionGraphStageInclusion K n h
local notation "o" => completeIdentityActionInputStageOriginalIso K n h
local notation "d" => completeIdentityFiniteRestriction K n h m

/-- The actual adjacent restriction between the literal original adic graphs. -/
def completeIdentityAdicGraphRestriction :
    completeIdentityActionGraphStage K n h m ⟶
      completeIdentityActionGraphStage K n h (m + 1) :=
  pullback.lift (r m) (p m ≫ (d) ≫ (o (m + 1)).hom) (by
    rw [Category.assoc, Category.assoc, completeIdentityActionInputStageOriginalIso_inclusion,
      completeIdentityFiniteRestriction_input,
      completeIdentityActionGraphStageOriginalProjection_input]
    exact pullback.condition)

/-- The restriction is over the unchanged complete graph. -/
@[reassoc] theorem completeIdentityAdicGraphRestriction_complete :
    completeIdentityAdicGraphRestriction K n h m ≫ r (m + 1) = r m :=
  pullback.lift_fst _ _ _

/-- Its full original source is the specified adjacent finite input restriction. -/
@[reassoc] theorem completeIdentityAdicGraphRestriction_source :
    completeIdentityAdicGraphRestriction K n h m ≫ p (m + 1) = p m ≫ (d) := by
  rw [completeIdentityActionGraphStageOriginalProjection, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ (o (m + 1)).inv = _
  rw [pullback.lift_snd, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original polygon-valued graph coordinates commute with adjacent restriction. -/
@[reassoc] theorem completeIdentityAdicGraphRestriction_target :
    completeIdentityAdicGraphRestriction K n h m ≫
        completeIdentityActionGraphStageOriginalLift K n h (m + 1) =
      completeIdentityActionGraphStageOriginalLift K n h m ≫ stageRestriction K m n h := by
  apply (cancel_mono (originalStageToCompatibleProj K n h (m + 1))).mp
  rw [Category.assoc, completeIdentityActionGraphStageOriginalLift_realization,
    Category.assoc, completeIdentityStageRestriction_toComplete,
    completeIdentityActionGraphStageOriginalLift_realization]
  change _ ≫ r (m + 1) ≫ completeIdentityActionGraphLift K n h =
    r m ≫ completeIdentityActionGraphLift K n h
  rw [completeIdentityAdicGraphRestriction_complete_assoc]

/-- The actual closed sections agree on every entire adjacent original thickening. -/
@[reassoc] theorem completeIdentityAdicGraphSection_restriction :
    (d) ≫ completeIdentityAdicGraphSection K n h (m + 1) =
      completeIdentityAdicGraphSection K n h m ≫ completeIdentityAdicGraphRestriction K n h m := by
  apply (cancel_mono (r (m + 1))).mp
  rw [Category.assoc, completeIdentityAdicGraphSection_complete,
    Category.assoc, completeIdentityAdicGraphRestriction_complete,
    completeIdentityAdicGraphSection_complete, completeIdentityFiniteToGraph_restriction]

end FLT.Mazur.PolygonInfinitesimalStages
