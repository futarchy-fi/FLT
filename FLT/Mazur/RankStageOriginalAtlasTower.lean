/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalAtlasErrors
public import FLT.Mazur.RankStageOriginalAffineBoundaryTower

/-!
# Actual boundary towers on all coordinates of one original atlas

The prescribed original boundary constructs the full invariant tower and all
original representatives. Every boundary and mixed equation has a coupled
error at every order, while the representatives retain their exact adic
compatibility in each unchanged source ring.
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
local instance atlasTowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance atlasTowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance atlasTowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  {ι : Type} [Finite ι] (b : ι → Γ(A, ⊤))
  (hb : ∀ i, A.basicOpen (b i) ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "U" i => rankStageOriginalAffineOpen (p := p) n (b i) (hb i)
attribute [local irreducible] rankStageCore

/-- The original boundary produces all coupled atlas errors and adic source differences. -/
theorem exists_rankStage_original_atlas_tower
    (h : ∀ k i, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen (b i) ≤
      rankStageCore e n a ha k)
    (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
    [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
    (t : SchemeEffectiveEpiSections.compatibleFunctions
      (CategoryTheory.Limits.pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ))
    (B : ι → Scheme.{0}) [∀ i, IsAffine (B i)]
    (gB : ∀ i, B i ⟶ X) (hgB : ∀ i, ⊤ ≤ gB i ⁻¹ᵁ (U i).1)
    (d : ∀ i, B i ⟶ J.subscheme)
    (hd : ∀ i, gB i ≫ (rankImageOpen (Over.mk p) n).ι = d i ≫ J.subschemeι)
    (M : ι → ι → Scheme.{0}) [∀ i j, IsAffine (M i j)]
    (gM gM' : ∀ i j, M i j ⟶ X)
    (hgM : ∀ i j, ⊤ ≤ gM i j ⁻¹ᵁ (U i).1)
    (hgM' : ∀ i j, ⊤ ≤ gM' i j ⁻¹ᵁ (U j).1)
    (δ : ∀ i j, M i j ⟶ D)
    (hδ : ∀ i j, δ i j ≫ p = gM i j ≫ (rankImageOpen (Over.mk p) n).ι)
    (hδ' : ∀ i j, δ i j ≫ q = gM' i j ≫ (rankImageOpen (Over.mk p) n).ι) :
    ∃ w : ℕ → ∀ i, Γ(X, (U i).1),
      (∀ k : ℕ,
        ((fun i ↦ (d i).appTop t.val), (0 : ∀ i j, Γ(M i j, ⊤))) -
          ((fun i ↦ (gB i).appLE (U i).1 ⊤ (hgB i) (w k i)),
            fun i j ↦ (gM i j).appLE (U i).1 ⊤ (hgM i j) (w k i) -
              (gM' i j).appLE (U j).1 ⊤ (hgM' i j) (w k j)) ∈
          BoundaryCorrectionIdeal.fullEquationIdeal
            (fun i ↦ ((I).comap (gB i)).ideal ⟨⊤, isAffineOpen_top (B i)⟩)
            (fun i j ↦ ((I).comap (gM i j)).ideal ⟨⊤, isAffineOpen_top (M i j)⟩) ^
              (k + 1)) ∧
      ∀ k l, k ≤ l → ∀ i, w l i - w k i ∈ ((I).ideal (U i)) ^ (k + 1) := by
  obtain ⟨v, hv, hc⟩ := exists_rankStage_original_boundary_tower e n a ha J hJ f hf t
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice fun k ↦
    exists_rankStage_original_atlas_error e n a ha b hb k (h k) J (v k) t.val (hv k)
      B gB hgB d hd M gM gM' hgM hgM' δ hδ hδ'
  refine ⟨w, fun k ↦ (hw k).2, fun k l hkl i ↦ ?_⟩
  apply rankStage_original_affine_difference e n a ha (b i) (hb i) hkl
    (h k i) (h l i) (v l) (w l i) (w k i) ((hw l).1 i)
  rw [hc k l hkl]
  exact (hw k).1 i

end FLT.Mazur.EquivalenceRelationOrderedFrames
