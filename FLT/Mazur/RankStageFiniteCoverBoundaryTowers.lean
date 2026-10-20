/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteCoreCover
public import FLT.Mazur.RankStageOriginalAffineCompatibility
public import FLT.Mazur.RankStageOriginalBoundaryTower

/-!
# Full boundary towers on a finite cover of the entire original rank locus

The original locus need not be finite. Its constructed finite cover carries
full boundary lifts and original affine representatives at every order.
Order compatibility holds on each domain; compatibility between distinct
cores is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coverTowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coverTowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coverTowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
  (h : ∀ k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤
    rankStageCore e n a ha k)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageCoreBoundaryIdeal rankStageCoreOriginalBoundaryMap

/-- Full boundary and order equations on one original coefficient domain. -/
def OriginalCoreBoundaryTowerOn
    (t : SchemeEffectiveEpiSections.compatibleFunctions
      (CategoryTheory.Limits.pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) : Prop :=
  ∃ (v : ∀ k, rankStageCoreInvariants e n a ha k) (w : ℕ → Γ(X, U.1)),
    (∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (v k).val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t.val) ∧
    (∀ k l (hkl : k ≤ l), rankStageCoreRestriction e n a ha hkl (v l) = v k) ∧
    (∀ k, (I ^ (k + 1)).subschemeι.app U.1 (w k) =
      rankStageCoreAffineCoefficient e n a ha b hb k (h k) (v k).val) ∧
    ∀ k l, k ≤ l → w l - w k ∈ ((I).ideal U) ^ (k + 1)

variable [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]

include hf in
/-- The original boundary constructs the entire tower on each selected domain. -/
theorem originalCoreBoundaryTowerOn_exists
    (t : SchemeEffectiveEpiSections.compatibleFunctions
      (CategoryTheory.Limits.pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    OriginalCoreBoundaryTowerOn e n a ha b hb h J hJ t := by
  obtain ⟨v, hv, hc⟩ := exists_rankStage_original_boundary_tower e n a ha J hJ f hf t
  obtain ⟨w, hw⟩ := exists_rankStage_original_affine_representatives e n a ha b hb h
    (fun k ↦ (v k).val)
  refine ⟨v, w, hv, hc, hw, fun k l hkl ↦ ?_⟩
  apply rankStage_original_affine_difference e n a ha b hb hkl
    (h k) (h l) (v l) (w l) (w k) (hw l)
  rw [hc k l hkl]
  exact hw k

attribute [local irreducible] OriginalCoreBoundaryTowerOn

include hf in
/-- Every original rank locus has finitely many actual full boundary towers covering it. -/
theorem exists_rankStage_finite_cover_boundary_towers
    (W : A.Opens) (s : Set A) (hsW : s ⊆ W) (hsn : s ⊆ exactRank (Over.mk p) n)
    (t : SchemeEffectiveEpiSections.compatibleFunctions
      (CategoryTheory.Limits.pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
      (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
      (hb : ∀ c : C, A.basicOpen c.val.2 ≤ rankImageOpen (Over.mk p) n)
      (h : ∀ (c : C) k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.val.2 ≤
        rankStageCore e n c.val.1 (ha c) k),
      (∀ c : C, A.basicOpen c.val.2 ≤ W) ∧
      s ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A) ∧
      ∀ c : C, OriginalCoreBoundaryTowerOn e n c.val.1 (ha c) c.val.2 (hb c) (h c) J hJ t := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_rankStage_original_finite_core_cover e n W s hsW hsn
  have hex (c : C) := hC c.val c.property
  choose ha hW hb h using hex
  refine ⟨C, ha, hb, h, hW, hcover, fun c ↦ ?_⟩
  exact originalCoreBoundaryTowerOn_exists e n c.val.1 (ha c) c.val.2 (hb c) (h c) J hJ f hf t

end FLT.Mazur.EquivalenceRelationOrderedFrames
