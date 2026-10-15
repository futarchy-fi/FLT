/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicClosed

/-!
# The literal adic graph retains the whole complete graph ideal

The closed stage presentation is cartesian over the original graph inclusion.
Its kernel is consequently the pullback of the full complete graph kernel,
including its nilpotents. No density assertion after adic reduction is used.
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
local notation "j" => completeIdentityActionAdicLiftSpaceMap K n h m
local notation "e" => completeIdentityActionGraphAdicEmbedding K n h m
local notation "v" => completeIdentityActionGraphStageInclusion K n h m
local notation "c" => completeIdentityActionGraphInclusion K n h
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "u" => completeIdentityActionInputStageInclusion K n h m
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m

/-- The stage lifting space retains both original coordinates injectively. -/
instance completeIdentityActionAdicLiftSpaceMap_mono : Mono (j) where
  right_cancellation x y he := by
    apply pullback.hom_ext
    · apply (cancel_mono (f)).mp
      simpa only [Category.assoc, completeIdentityActionAdicLiftSpaceMap,
        pullback.lift_fst] using congrArg (fun z ↦ z ≫ pullback.fst (a) (g)) he
    · apply (cancel_mono (r)).mp
      simpa only [Category.assoc, completeIdentityActionAdicLiftSpaceMap,
        pullback.lift_snd] using congrArg (fun z ↦ z ≫ pullback.snd (a) (g)) he

/-- The entire closed stage graph is the literal pullback of the complete graph inclusion. -/
theorem completeIdentityActionGraphAdicEmbedding_isPullback : IsPullback (e) (v) (j) (c) := by
  apply IsPullback.mk' (completeIdentityActionGraphAdicEmbedding_complete K n h m)
  · intro T x y _ hv
    exact (cancel_mono (v)).mp hv
  · intro T x y he
    have hp : y ≫ (p) = (x ≫ pullback.fst _ _ ≫ (o).hom) ≫ (u) := by
      rw [Category.assoc, Category.assoc,
        completeIdentityActionInputStageOriginalIso_inclusion]
      simpa only [Category.assoc, completeIdentityActionAdicLiftSpaceMap,
        pullback.lift_fst, completeIdentityActionGraphProjection] using
        (congrArg (fun z ↦ z ≫ pullback.fst (a) (g)) he).symm
    let z := pullback.lift y (x ≫ pullback.fst _ _ ≫ (o).hom) hp
    have hz : z ≫ (v) = y := pullback.lift_fst _ _ _
    refine ⟨z, ?_, hz⟩
    apply (cancel_mono (j)).mp
    rw [Category.assoc, completeIdentityActionGraphAdicEmbedding_complete,
      ← Category.assoc, hz, he]

/-- The full original graph ideal pulls back exactly, without a radical or new image. -/
theorem completeIdentityActionGraphAdicEmbedding_ideal : (c).ker.comap (j) = (e).ker := by
  have H := completeIdentityActionGraphAdicEmbedding_isPullback K n h m
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

/-- The literal quotient scheme of the pulled-back original ideal is the actual adic graph. -/
def completeIdentityActionGraphAdicIdealIso :
    completeIdentityActionGraphStage K n h m ≅ ((c).ker.comap (j)).subscheme :=
  (asIso (e).toImage) ≪≫ BaseAdicThickening.subschemeCongr
    (completeIdentityActionGraphAdicEmbedding_ideal K n h m).symm

end FLT.Mazur.PolygonInfinitesimalStages
