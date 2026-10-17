/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteGraphCoherence

/-!
# Actual sections of every original adic graph projection

The whole finite-input graph maps lift to the literal base-changed graph.
They split its projection onto the unchanged original input, and their
polygon coordinates are the original universal scaling maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "r" => completeIdentityActionGraphStageInclusion K n h m

/-- The full original finite input maps into the literal adic graph, without taking an image. -/
def completeIdentityAdicGraphSection :
    scalingParameterFamily (A) (t) n h ⟶ completeIdentityActionGraphStage K n h m :=
  pullback.lift (completeIdentityFiniteToGraph K n h m) (o).hom (by
    rw [completeIdentityFiniteToGraph_source,
      completeIdentityActionInputStageOriginalIso_inclusion])

/-- Its complete graph realization is the previously constructed full finite lift. -/
@[reassoc] theorem completeIdentityAdicGraphSection_complete :
    completeIdentityAdicGraphSection K n h m ≫ (r) =
      completeIdentityFiniteToGraph K n h m := pullback.lift_fst _ _ _

/-- The unchanged original adic projection is split by the constructed whole-input map. -/
@[reassoc] theorem completeIdentityAdicGraphSection_projection :
    completeIdentityAdicGraphSection K n h m ≫ (p) = 𝟙 _ := by
  rw [completeIdentityActionGraphStageOriginalProjection, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ (o).inv = _
  rw [pullback.lift_snd, Iso.hom_inv_id]

/-- The section embeds the whole original input as a closed subscheme of the literal graph. -/
instance completeIdentityAdicGraphSection_closed :
    IsClosedImmersion (completeIdentityAdicGraphSection K n h m) := by
  have : IsClosedImmersion (completeIdentityAdicGraphSection K n h m ≫ (p)) := by
    rw [completeIdentityAdicGraphSection_projection]
    infer_instance
  exact IsClosedImmersion.of_comp _ (p)

/-- The original projection is a split epimorphism at every finite order. -/
instance completeIdentityAdicGraphProjection_split : IsSplitEpi (p) :=
  IsSplitEpi.mk' ⟨completeIdentityAdicGraphSection K n h m,
    completeIdentityAdicGraphSection_projection K n h m⟩

/-- The section's complete polygon coordinate is the unchanged original finite scaling. -/
@[reassoc] theorem completeIdentityAdicGraphSection_realization :
    completeIdentityAdicGraphSection K n h m ≫
        completeIdentityActionGraphStageOriginalLift K n h m ≫
          originalStageToCompatibleProj K n h m = completeIdentityFiniteScaling K n h m := by
  rw [completeIdentityActionGraphStageOriginalLift_realization]
  change _ ≫ (r) ≫ completeIdentityActionGraphLift K n h = _
  rw [completeIdentityAdicGraphSection_complete_assoc, completeIdentityFiniteToGraph_target]

/-- The original finite polygon coordinate, before realization, is the universal scaling. -/
@[reassoc] theorem completeIdentityAdicGraphSection_target :
    completeIdentityAdicGraphSection K n h m ≫
        completeIdentityActionGraphStageOriginalLift K n h m =
      universalScaling (A) (t) n h := by
  apply (cancel_mono (originalStageToCompatibleProj K n h m)).mp
  rw [Category.assoc, completeIdentityAdicGraphSection_realization]
  rfl

/-- The literal adic projection retains every original function, including nilpotents. -/
instance completeIdentityAdicGraphProjection_schematic : IsSchemeTheoreticallyDominant (p) := by
  constructor
  apply le_bot_iff.mp
  calc
    (p).ker ≤ (completeIdentityAdicGraphSection K n h m ≫ (p)).ker :=
      Scheme.Hom.le_ker_comp _ _
    _ = ⊥ := by rw [completeIdentityAdicGraphSection_projection, Scheme.Hom.ker_eq_bot]

end FLT.Mazur.PolygonInfinitesimalStages
