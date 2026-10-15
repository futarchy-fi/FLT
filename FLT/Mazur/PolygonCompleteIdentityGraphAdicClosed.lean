/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicParameter

/-!
# The literal adic graph inside the original cubic lifting space

The adic graph is a closed subscheme of the pullback of the original cubic
action and contraction. Both coordinates are the original stage morphisms;
the construction does not take a new schematic image after base change.
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
local notation "f" => completeIdentityFiniteInput K n h 0 m
local notation "r" => originalStageToCompatibleProj K n h m
local notation "a" => completeIdentityActionTarget K n h 0
local notation "g" => completePointToIntegralCubic K n h 0
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "l" => completeIdentityActionGraphStageOriginalLift K n h m

instance completeIdentityFiniteInput_closed : IsClosedImmersion (f) :=
  MorphismProperty.of_isPullback (completeIdentityFiniteInput_base_isPullback K n h 0 m).flip
    (inferInstanceAs (IsClosedImmersion (baseToSeries K m)))

instance completeIdentityActionGraphStageInclusion_closed :
    IsClosedImmersion (completeIdentityActionGraphStageInclusion K n h m) := by
  unfold completeIdentityActionGraphStageInclusion completeIdentityActionInputStageInclusion
  infer_instance

/-- The full original stage lifting space, retaining the original cubic equality. -/
abbrev completeIdentityActionAdicLiftSpace : Scheme := pullback ((f) ≫ (a)) ((r) ≫ (g))

/-- The stage lifting space maps into the unchanged complete lifting space. -/
def completeIdentityActionAdicLiftSpaceMap :
    completeIdentityActionAdicLiftSpace K n h m ⟶ completeIdentityActionLiftSpace K n h :=
  pullback.lift (pullback.fst _ _ ≫ (f)) (pullback.snd _ _ ≫ (r))
    (by simpa only [Category.assoc] using
      (show pullback.fst ((f) ≫ (a)) ((r) ≫ (g)) ≫ ((f) ≫ (a)) =
        pullback.snd ((f) ≫ (a)) ((r) ≫ (g)) ≫ ((r) ≫ (g)) from pullback.condition))

/-- The actual stage graph has its two original coordinates in this lifting space. -/
def completeIdentityActionGraphAdicEmbedding :
    completeIdentityActionGraphStage K n h m ⟶ completeIdentityActionAdicLiftSpace K n h m :=
  pullback.lift (p) (l) (by
    rw [completeIdentityActionGraphStageOriginalLift_contraction,
      completeIdentityActionGraphStageOriginalProjection_input_assoc])

@[reassoc] theorem completeIdentityActionGraphAdicEmbedding_fst :
    completeIdentityActionGraphAdicEmbedding K n h m ≫ pullback.fst _ _ = (p) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem completeIdentityActionGraphAdicEmbedding_snd :
    completeIdentityActionGraphAdicEmbedding K n h m ≫ pullback.snd _ _ = (l) :=
  pullback.lift_snd _ _ _

/-- The embedding retains the original full closed graph, with no image/base-change exchange. -/
@[reassoc] theorem completeIdentityActionGraphAdicEmbedding_complete :
    completeIdentityActionGraphAdicEmbedding K n h m ≫
        completeIdentityActionAdicLiftSpaceMap K n h m =
      completeIdentityActionGraphStageInclusion K n h m ≫
        completeIdentityActionGraphInclusion K n h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityActionAdicLiftSpaceMap, pullback.lift_fst,
      completeIdentityActionGraphAdicEmbedding_fst_assoc,
      completeIdentityActionGraphStageOriginalProjection_input]
    exact pullback.condition.symm
  · simp only [Category.assoc, completeIdentityActionAdicLiftSpaceMap, pullback.lift_snd,
      completeIdentityActionGraphAdicEmbedding_snd_assoc,
      completeIdentityActionGraphStageOriginalLift_realization]
    rfl

instance completeIdentityActionAdicLiftSpaceMap_separated :
    IsSeparated (completeIdentityActionAdicLiftSpaceMap K n h m) := by
  let _ := completePointToIntegralCubic_proper K n h (0 : Fin n)
  have : IsSeparated (completeIdentityActionAdicLiftSpaceMap K n h m ≫
      pullback.fst (a) (g)) := by
    rw [completeIdentityActionAdicLiftSpaceMap, pullback.lift_fst]
    infer_instance
  exact IsSeparated.of_comp _ (pullback.fst (a) (g))

/-- The literal adic graph has a full closed presentation in the original stage lifting space. -/
instance completeIdentityActionGraphAdicEmbedding_closed :
    IsClosedImmersion (completeIdentityActionGraphAdicEmbedding K n h m) := by
  have : IsClosedImmersion (completeIdentityActionGraphAdicEmbedding K n h m ≫
      completeIdentityActionAdicLiftSpaceMap K n h m) := by
    rw [completeIdentityActionGraphAdicEmbedding_complete]
    infer_instance
  exact IsClosedImmersion.of_comp _ (completeIdentityActionAdicLiftSpaceMap K n h m)

end FLT.Mazur.PolygonInfinitesimalStages
