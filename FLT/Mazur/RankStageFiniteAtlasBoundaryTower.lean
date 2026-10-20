/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteAtlasCoverage
public import FLT.Mazur.RankStageOriginalAffineCompatibility
public import FLT.Mazur.RankStageOriginalBoundaryTower

/-!
# Constructed common boundary towers through finite original atlas loci

One shared core is chosen for all prescribed finite loci before the boundary
is lifted. The full original boundary then constructs simultaneous representatives
on all the selected original neighborhoods with exact adic differences.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteTowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteTowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteTowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable (n : ℕ) {ι : Type} [Finite ι]
  (W : ι → A.Opens) (s : ι → Set A) (hs : ∀ i, (s i).Finite)
  (hsW : ∀ i, s i ⊆ W i) (hsn : ∀ i, s i ⊆ exactRank (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageCoreBoundaryIdeal rankStageCoreOriginalBoundaryMap

include hs hsW hsn hf in
/-- Finite original chart loci construct one shared full boundary tower and all representatives. -/
theorem exists_rankStage_original_finite_atlas_boundary_tower
    (t : SchemeEffectiveEpiSections.compatibleFunctions
      (CategoryTheory.Limits.pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (b : ι → Γ(A, ⊤)) (hb : ∀ i, A.basicOpen (b i) ≤ rankImageOpen (Over.mk p) n)
      (h : ∀ k i, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen (b i) ≤
        rankStageCore e n a ha k),
      (∀ i, s i ⊆ A.basicOpen (b i)) ∧ (∀ i, A.basicOpen (b i) ≤ W i) ∧
      ∃ (v : ∀ k, rankStageCoreInvariants e n a ha k)
        (w : ℕ → ∀ i, Γ(X, (rankStageOriginalAffineOpen (p := p) n (b i) (hb i)).1)),
        (∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (v k).val =
          (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t.val) ∧
        (∀ k l (hkl : k ≤ l), rankStageCoreRestriction e n a ha hkl (v l) = v k) ∧
        (∀ k i, (I ^ (k + 1)).subschemeι.app
          (rankStageOriginalAffineOpen (p := p) n (b i) (hb i)).1 (w k i) =
          rankStageCoreAffineCoefficient e n a ha (b i) (hb i) k (h k i) (v k).val) ∧
        ∀ k l, k ≤ l → ∀ i, w l i - w k i ∈
          ((I).ideal (rankStageOriginalAffineOpen (p := p) n (b i) (hb i))) ^ (k + 1) := by
  obtain ⟨a, ha, b, hsb, hbW, hb, h⟩ :=
    exists_rankStage_original_finite_atlas e n W s hs hsW hsn
  obtain ⟨v, hv, hc⟩ := exists_rankStage_original_boundary_tower e n a ha J hJ f hf t
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice fun k ↦ Classical.axiomOfChoice fun i ↦
    exists_rankStage_original_affine_representative e n a ha (b i) (hb i) k (h k i)
      (v k).val
  refine ⟨a, ha, b, hb, h, hsb, hbW, v, w, hv, hc, hw, fun k l hkl i ↦ ?_⟩
  apply rankStage_original_affine_difference e n a ha (b i) (hb i) hkl
    (h k i) (h l i) (v l) (w l i) (w k i) (hw l i)
  rw [hc k l hkl]
  exact hw k i

end FLT.Mazur.EquivalenceRelationOrderedFrames
