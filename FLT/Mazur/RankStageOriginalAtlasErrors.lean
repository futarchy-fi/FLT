/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalCoordinateErrors
public import FLT.Mazur.BoundaryCorrectionAdicEquationIdeal

/-!
# Simultaneous original atlas representatives and coupled errors

All original boundary and ordered-pair mixed coordinates in one core are
retained in a single ideal-power error. The representatives are constructed
simultaneously from the full core coefficient. The fixed coordinate ideals
are pulled back before choosing the infinitesimal order.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance atlasErrorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance atlasErrorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance atlasErrorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  {ι : Type} [Finite ι] (b : ι → Γ(A, ⊤))
  (hb : ∀ i, A.basicOpen (b i) ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "U" i => rankStageOriginalAffineOpen (p := p) n (b i) (hb i)
attribute [local irreducible] rankStageCore

/-- One full core value constructs representatives and the entire original atlas error. -/
theorem exists_rankStage_original_atlas_error (k : ℕ)
    (h : ∀ i, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen (b i) ≤
      rankStageCore e n a ha k)
    (J : A.IdealSheafData) (v : rankStageCoreInvariants e n a ha k)
    (t : Γ(J.subscheme, ⊤))
    (hv : (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t)
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
    ∃ w : ∀ i, Γ(X, (U i).1),
      (∀ i, (I ^ (k + 1)).subschemeι.app (U i).1 (w i) =
        rankStageCoreAffineCoefficient e n a ha (b i) (hb i) k (h i) v.val) ∧
      ((fun i ↦ (d i).appTop t), (0 : ∀ i j, Γ(M i j, ⊤))) -
        ((fun i ↦ (gB i).appLE (U i).1 ⊤ (hgB i) (w i)),
          fun i j ↦ (gM i j).appLE (U i).1 ⊤ (hgM i j) (w i) -
            (gM' i j).appLE (U j).1 ⊤ (hgM' i j) (w j)) ∈
        BoundaryCorrectionIdeal.fullEquationIdeal
          (fun i ↦ ((I).comap (gB i)).ideal ⟨⊤, isAffineOpen_top (B i)⟩)
          (fun i j ↦ ((I).comap (gM i j)).ideal ⟨⊤, isAffineOpen_top (M i j)⟩) ^
            (k + 1) := by
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice fun i ↦
    exists_rankStage_original_affine_representative e n a ha (b i) (hb i) k (h i) v.val
  refine ⟨w, hw, ?_⟩
  rw [BoundaryCorrectionIdeal.mem_fullEquationIdeal_pow]
  constructor
  · intro i
    exact rankStage_original_boundary_error e n a ha (b i) (hb i) k (h i) J v t hv
      (w i) (hw i) (gB i) (hgB i) (d i) (hd i)
  · intro i j
    change 0 - ((gM i j).appLE (U i).1 ⊤ (hgM i j) (w i) -
      (gM' i j).appLE (U j).1 ⊤ (hgM' i j) (w j)) ∈ _
    rw [zero_sub]
    apply Submodule.neg_mem
    exact rankStage_original_mixed_error e n a ha (b i) (hb i) k (h i)
      (b j) (hb j) (h j) v (w i) (w j) (hw i) (hw j)
      (gM i j) (gM' i j) (hgM i j) (hgM' i j) (δ i j) (hδ i j) (hδ' i j)

end FLT.Mazur.EquivalenceRelationOrderedFrames
