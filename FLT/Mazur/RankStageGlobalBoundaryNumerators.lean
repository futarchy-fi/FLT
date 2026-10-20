/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageInvariantNormParameters
public import FLT.Mazur.RankStageFullBoundaryGluing
public import FLT.Mazur.SchemeRelationQcqsIdealBoundaryNumerator

/-!
# Global full-boundary numerators from actual rank-core lifts

Each local invariant lift extends to the entire nonaffine rank stage after
multiplication by a power of its constructed global norm parameter. Its
boundary is exactly the same power times the prescribed original boundary.
The exponent is constructed at one order; no bound over all orders is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections IdealSheafClosedTransitions
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance globalNumOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance globalNumOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance globalNumOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (ha c) k) = ⊤)
local notation "X" k => rankThickening (Over.mk p) n k
attribute [local irreducible] rankStageCore rankStageNormParameter

include hc in
/-- The constructed finite affine core cover proves compactness of the whole rank stage. -/
theorem rankStage_compact_of_core_cover (k : ℕ) : CompactSpace (X k) := by
  let V := (X k).openCoverOfIsOpenCover
    (fun c : C ↦ rankStageCore e n c.val.1 (ha c) k) (hc k)
  let _ : Finite V.I₀ := by dsimp [V]; infer_instance
  have hV : ∀ c, CompactSpace (V.X c) := by
    intro c
    let _ : IsAffine (V.X c) := rankStageCore_affine e n c.val.1 (ha c) k
    infer_instance
  exact V.compactSpace

variable (a : Γ(A, ⊤)) (ha' : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (k : ℕ)
local notation "U" => rankStageCore e n a ha' k
local notation "I" => rankStageBoundaryIdeal (p := p) n k J
local notation "K" => rankStageCoreBoundaryIdeal e n a ha' J k
local notation "r" => rankStageNormParameter e n C ha hc a k

/-- The core boundary map factors through the whole stage boundary with the original ideal. -/
theorem rankStageCoreBoundary_full_map :
    map ((I).comap (U).ι) I (U).ι rfl ≫ rankStageFullOriginalBoundaryMap n J k =
      rankStageCoreOriginalBoundaryMap e n a ha' J k := by
  apply (cancel_mono J.subschemeι).mp
  simp only [rankStageCoreOriginalBoundaryMap, rankStageFullOriginalBoundaryMap,
    map_inclusion, Category.assoc, map_inclusion_assoc, rankStageCoreOriginalMap,
    rankStageCoreBoundaryIdeal]

/-- Every actual core lift has an exact global full-boundary invariant numerator. -/
theorem exists_rankStage_global_boundary_numerator
    (v : rankStageCoreInvariants e n a ha' k) (t : Γ(J.subscheme, ⊤))
    (hv : (K).subschemeι.appTop v.val =
      (rankStageCoreOriginalBoundaryMap e n a ha' J k).appTop t) :
    ∃ (N : ℕ)
      (w : compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k)),
      (I).subschemeι.appTop w.val = ((I).subschemeι.appTop (r).val) ^ N *
        (rankStageFullOriginalBoundaryMap n J k).appTop t ∧
      (U).ι.appTop w.val = ((U).ι.appTop (r).val) ^ N * v.val := by
  let _ := rankStageFirst_finite (p := p) n k
  let _ := rankStage_compact_of_core_cover e n C ha hc k
  let _ : QuasiSeparated (rankThickeningMap (Over.mk p) n k) := by
    unfold rankThickeningMap
    infer_instance
  let _ := quasiSeparatedSpace_of_quasiSeparated (rankThickeningMap (Over.mk p) n k)
  let _ := QuasiCompact.compactSpace_of_compactSpace (rankStageFirst (p := p) n k)
  let _ := quasiSeparatedSpace_of_quasiSeparated (rankStageFirst (p := p) n k)
  let _ := QuasiCompact.compactSpace_of_compactSpace (I).subschemeι
  let _ := quasiSeparatedSpace_of_quasiSeparated (I).subschemeι
  apply SchemeRelationQcqsBoundaryNumerator.exists_ideal_boundary_numerator _ _ r I U
    (rankStageCore_invariant e n a ha' k)
    (rankStageNormParameter_basicOpen e n C ha hc a ha' k).symm v
    ((rankStageFullOriginalBoundaryMap n J k).appTop t)
  change (K).subschemeι.appTop v.val = _
  rw [hv]
  change _ = (map ((I).comap (U).ι) I (U).ι rfl ≫
    rankStageFullOriginalBoundaryMap n J k).appTop t
  rw [rankStageCoreBoundary_full_map]
  rfl

/-- A boundary-zero core error extends to a full stage boundary-zero invariant numerator. -/
theorem exists_rankStage_global_kernel_numerator
    (v : rankStageCoreInvariants e n a ha' k)
    (hv : (K).subschemeι.appTop v.val = 0) :
    ∃ (N : ℕ)
      (w : compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k)),
      (I).subschemeι.appTop w.val = 0 ∧
      (U).ι.appTop w.val = ((U).ι.appTop (r).val) ^ N * v.val := by
  obtain ⟨N, w, hw, he⟩ := exists_rankStage_global_boundary_numerator e n C ha hc a ha' J k
    v 0 (by simpa only [map_zero] using hv)
  exact ⟨N, w, by simpa only [map_zero, mul_zero] using hw, he⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
