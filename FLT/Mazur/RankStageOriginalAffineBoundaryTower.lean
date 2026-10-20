/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalAffineCompatibility
public import FLT.Mazur.RankStageOriginalBoundaryTower

/-!
# Full prescribed boundary towers in an original affine coefficient ring

Every original point has a principal neighborhood on which the constructed
full boundary tower has actual original representatives. These representatives
are compatible modulo the original rank ideal powers. The prescribed boundary
is retained on every core, including its nonreduced structure.
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
local instance affineTowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance affineTowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance affineTowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha
local notation "B" => rankStageCoreBoundaryIdeal e n a ha J
local notation "T" => SchemeEffectiveEpiSections.compatibleFunctions
  (CategoryTheory.Limits.pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ)

attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageCoreBoundaryIdeal rankStageCoreOriginalBoundaryMap

include hf in
/-- Prescribed full boundary towers have original affine representatives with adic differences. -/
theorem exists_rankStage_original_affine_boundary_tower
    (y : rankThickening (Over.mk p) n 0) (hy : y ∈ C 0) (t : T) :
    ∃ (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n),
      rankThickeningMap (Over.mk p) n 0 y ∈ A.basicOpen b ∧
      ∃ h : ∀ k : ℕ, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C k,
      ∃ (v : ∀ k : ℕ, rankStageCoreInvariants e n a ha k)
        (w : ℕ → Γ(X, (rankStageOriginalAffineOpen (p := p) n b hb).1)),
        (∀ k, (B k).subschemeι.appTop (v k).val =
          (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t.val) ∧
        (∀ k l (hkl : k ≤ l), rankStageCoreRestriction e n a ha hkl (v l) = v k) ∧
        (∀ k, (I ^ (k + 1)).subschemeι.app
          (rankStageOriginalAffineOpen (p := p) n b hb).1 (w k) =
          rankStageCoreAffineCoefficient e n a ha b hb k (h k) (v k).val) ∧
        ∀ k l, k ≤ l → w l - w k ∈
          ((I).ideal (rankStageOriginalAffineOpen (p := p) n b hb)) ^ (k + 1) := by
  obtain ⟨b, hyb, hb, h⟩ := exists_rankStage_core_original_principal e n a ha y hy
  obtain ⟨v, hboundary, hcompat⟩ :=
    exists_rankStage_original_boundary_tower e n a ha J hJ f hf t
  obtain ⟨w, hw⟩ := exists_rankStage_original_affine_representatives e n a ha b hb h
    (fun k ↦ (v k).val)
  refine ⟨b, hb, hyb, h, v, w, hboundary, hcompat, hw, fun k l hkl ↦ ?_⟩
  apply rankStage_original_affine_difference e n a ha b hb hkl (h k) (h l) (v l)
    (w l) (w k) (hw l)
  rw [hcompat]
  exact hw k

end FLT.Mazur.EquivalenceRelationOrderedFrames
