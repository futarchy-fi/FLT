/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphRotationLaws
public import FLT.Mazur.PolygonCompleteIdentityAdicGraphSections

/-!
# Rotation of the literal adic graphs

The complete graph automorphisms restrict to the original adic base changes.
Their coordinates are the original finite polygon rotations, and their
sections are equivariant on the whole finite input.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "r" => rotation (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h b
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "j" => completeIdentityActionGraphStageInclusion K n h m
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "R" => completeIdentityGraphRotation K n h b

/-- Rotation on the actual adic graph is induced from the unchanged complete graph. -/
def completeIdentityAdicGraphRotation :
    completeIdentityActionGraphStage K n h m ⟶ completeIdentityActionGraphStage K n h m :=
  pullback.lift ((j) ≫ (R)) ((p) ≫ (r) ≫ (o).hom) (by
    rw [Category.assoc, completeIdentityGraphRotation_source,
      Category.assoc, Category.assoc, completeIdentityActionInputStageOriginalIso_inclusion,
      completeIdentityFiniteInput_rotation,
      completeIdentityActionGraphStageOriginalProjection_input_assoc,
      pullback.condition_assoc])

/-- The adic rotation is the restriction of the full original graph rotation. -/
@[reassoc] theorem completeIdentityAdicGraphRotation_complete :
    completeIdentityAdicGraphRotation K n h m b ≫ (j) = (j) ≫ (R) :=
  pullback.lift_fst _ _ _

/-- The entire original finite source rotates by its original cyclic action. -/
@[reassoc] theorem completeIdentityAdicGraphRotation_source :
    completeIdentityAdicGraphRotation K n h m b ≫ (p) = (p) ≫ (r) := by
  rw [completeIdentityActionGraphStageOriginalProjection, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ (o).inv = _
  rw [pullback.lift_snd, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The target is the original finite rotation before complete realization. -/
@[reassoc] theorem completeIdentityAdicGraphRotation_target :
    completeIdentityAdicGraphRotation K n h m b ≫
        completeIdentityActionGraphStageOriginalLift K n h m =
      completeIdentityActionGraphStageOriginalLift K n h m ≫ stageRotation K n h m b := by
  apply (cancel_mono (originalStageToCompatibleProj K n h m)).mp
  rw [Category.assoc, completeIdentityActionGraphStageOriginalLift_realization,
    Category.assoc, ← originalStageToCompatibleProj_rotation,
    completeIdentityActionGraphStageOriginalLift_realization_assoc]
  change _ ≫ (j) ≫ completeIdentityActionGraphLift K n h = _
  rw [completeIdentityAdicGraphRotation_complete_assoc, completeIdentityGraphRotation_target]
  simp only [completeIdentityActionGraphStageLift, Category.assoc]

/-- The full original finite lift commutes with rotation in the unchanged complete graph. -/
@[reassoc] theorem completeIdentityFiniteToGraph_rotation :
    (r) ≫ completeIdentityFiniteToGraph K n h m =
      completeIdentityFiniteToGraph K n h m ≫ (R) := by
  apply completeIdentityGraph_hom_ext
  · rw [Category.assoc, completeIdentityFiniteToGraph_source,
      Category.assoc, completeIdentityGraphRotation_source,
      completeIdentityFiniteToGraph_source_assoc, completeIdentityFiniteInput_rotation]
  · rw [Category.assoc, completeIdentityFiniteToGraph_target,
      Category.assoc, completeIdentityGraphRotation_target,
      completeIdentityFiniteToGraph_target_assoc, completeIdentityFiniteScaling_rotation]

/-- The actual whole-input adic sections respect the original cyclic action. -/
@[reassoc] theorem completeIdentityAdicGraphSection_rotation :
    (r) ≫ completeIdentityAdicGraphSection K n h m =
      completeIdentityAdicGraphSection K n h m ≫ completeIdentityAdicGraphRotation K n h m b := by
  apply (cancel_mono (j)).mp
  rw [Category.assoc, completeIdentityAdicGraphSection_complete,
    Category.assoc, completeIdentityAdicGraphRotation_complete,
    completeIdentityAdicGraphSection_complete_assoc, completeIdentityFiniteToGraph_rotation]

end FLT.Mazur.PolygonInfinitesimalStages
