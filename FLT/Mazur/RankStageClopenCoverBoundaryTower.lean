/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantClopenSelectionPullback
public import FLT.Mazur.RankStageClopenCoreExtension
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# Global compatible boundary towers from finite clopen rank-core covers

A fixed priority partition selects the actual local lifts of the original
boundary section. This constructs a global full invariant lift at every order,
with ordinary compatibility. Local overlap agreement is not an assumption.
The construction does not extend or algebraize the tower on the original source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance clopenCoverOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance clopenCoverOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance clopenCoverOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) {m : ℕ} (a : Fin m → Γ(A, ⊤))
  (ha : ∀ i, A.basicOpen (a i) ≤ rankImageOpen (Over.mk p) n)
  (hclosed : ∀ i,
    IsClosed (rankStageCore e n (a i) (ha i) 0 : Set (rankThickening (Over.mk p) n 0)))
  (hcover : (⨆ i, rankStageCore e n (a i) (ha i) 0) = ⊤)
local notation "U" i:max k:max => rankStageCore e n (a i) (ha i) k
attribute [local irreducible] rankStageCore

include hcover in
/-- A core cover at order zero covers every full rank thickening. -/
theorem rankStageCore_cover_of_zero (k : ℕ) : (⨆ i, U i k) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := rankStageTransition_surjective n (Nat.zero_le k) x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show y ∈ (⨆ i, U i 0) from hcover.symm ▸ trivial)
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  change y ∈ rankStageTransition (Over.mk p) n (Nat.zero_le k) ⁻¹ᵁ U i k
  rw [rankStageCore_preimage]
  exact hi

variable (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
local notation "v" i:max => rankStageChosenBoundaryCoreTower e n (a i) (ha i) J hJ f hf t
local notation "hc" i:max k:max => rankStageCore_isClosed_of_zero e n (a i) (ha i) (hclosed i) k
local notation "hi" i:max k:max => rankStageCore_invariant e n (a i) (ha i) k
local notation "cov" k:max => rankStageCore_cover_of_zero e n a ha hcover k
attribute [local irreducible] rankStageChosenBoundaryCoreTower rankStageGlobalCoreRestriction
  rankStageCoreRestriction rankStageInvariantTransition
  rankStageCoreOriginalBoundaryMap rankStageFullOriginalBoundaryMap

/-- Select actual original-boundary lifts using the same chart priority at every order. -/
def rankStageClopenCoverChosenLift (k : ℕ) : rankStageInvariants e n k :=
  InvariantClopenCoverSelection.select _ _ (fun i ↦ U i k)
    (fun i ↦ hi i k) (fun i ↦ hc i k) (cov k) (fun i ↦ (v i).val k)

/-- The selected full coefficients satisfy every order-transition equation. -/
theorem rankStageClopenCoverChosenLift_transition {k l : ℕ} (h : k ≤ l) :
    rankStageInvariantTransition e n h
        (rankStageClopenCoverChosenLift e n a ha hclosed hcover J hJ f hf t l) =
      rankStageClopenCoverChosenLift e n a ha hclosed hcover J hJ f hf t k := by
  apply Subtype.ext
  rw [rankStageInvariantTransition_val]
  apply InvariantClopenCoverSelection.select_pullback
    (rankStageFirst (p := p) n l) (rankStageSecond e n l)
    (rankStageFirst (p := p) n k) (rankStageSecond e n k)
    (fun i ↦ U i l) (fun i ↦ hi i l) (fun i ↦ hc i l) (cov l)
    (fun i ↦ U i k) (fun i ↦ hi i k) (fun i ↦ hc i k) (cov k)
    (rankStageTransition (Over.mk p) n h) (fun i ↦ rankStageCore_preimage e n _ _ h)
    (fun i ↦ (v i).val l) (fun i ↦ (v i).val k)
  intro i
  simpa only [rankStageCoreRestriction_val, rankStageCoreMap] using
    congrArg Subtype.val ((v i).property k l h)

/-- The selected coefficient retains the full original boundary at each order. -/
theorem rankStageClopenCoverChosenLift_boundary (k : ℕ) :
    (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop
        (rankStageClopenCoverChosenLift e n a ha hclosed hcover J hJ f hf t k).val =
      (rankStageFullOriginalBoundaryMap n J k).appTop t.val := by
  apply InvariantClopenCoverSelection.select_boundary
  intro i
  have hb := rankStageChosenBoundaryCoreTower_boundary e n (a i) (ha i) J hJ f hf t k
  simp only [rankStageCoreBoundaryIdeal] at hb
  refine hb.trans ?_
  change (rankStageCoreOriginalBoundaryMap e n (a i) (ha i) J k).appTop t.val =
    (IdealSheafClosedTransitions.map _ _ (U i k).ι rfl ≫
      rankStageFullOriginalBoundaryMap n J k).appTop t.val
  rw [rankStageCoreBoundary_full_map]
  rfl

include hf hclosed hcover in
/-- Construct a global compatible full boundary tower without assuming local overlap agreement. -/
theorem exists_rankStage_clopen_cover_boundary_tower :
    ∃ w : ∀ k, rankStageInvariants e n k,
      (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
      ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (w k).val =
        (rankStageFullOriginalBoundaryMap n J k).appTop t.val :=
  ⟨rankStageClopenCoverChosenLift e n a ha hclosed hcover J hJ f hf t,
    fun _ _ h ↦ rankStageClopenCoverChosenLift_transition e n a ha hclosed hcover J hJ f hf t h,
    rankStageClopenCoverChosenLift_boundary e n a ha hclosed hcover J hJ f hf t⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
