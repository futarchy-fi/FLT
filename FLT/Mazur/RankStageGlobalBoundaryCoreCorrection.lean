/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCompatibleKernelObstruction
public import FLT.Mazur.RankStageInvariantOverlapErrors

/-!
# Exact homogeneous corrections relative to a full global boundary tower

Subtracting a global lift from each local lift constructs corrections on the
whole named cores. These corrections preserve all full boundary equations,
commute with every order transition, and recover the actual overlap cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance globalCorrectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance globalCorrectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance globalCorrectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition

/-- The exact correction on a whole core, with ordinary compatibility built into its type. -/
def rankStageGlobalBoundaryCoreCorrection
    (v : rankStageCompatibleCoreInvariants e n a ha) (w : rankStageCompatibleInvariants e n) :
    rankStageCompatibleCoreInvariants e n a ha :=
  v - rankStageCompatibleCoreRestriction e n a ha w

/-- Subtracting the correction gives precisely the restricted global tower. -/
theorem rankStageGlobalBoundaryCoreCorrection_corrects
    (v : rankStageCompatibleCoreInvariants e n a ha) (w : rankStageCompatibleInvariants e n) :
    v - rankStageGlobalBoundaryCoreCorrection e n a ha v w =
      rankStageCompatibleCoreRestriction e n a ha w := sub_sub_cancel _ _

/-- Restricting a full global boundary lift preserves the prescribed original core boundary. -/
theorem rankStageGlobalCoreRestriction_boundary (J : A.IdealSheafData) (k : ℕ)
    (w : rankStageInvariants e n k) (t : Γ(J.subscheme, ⊤))
    (hw : (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop w.val =
      (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t) :
    (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
        (rankStageGlobalCoreRestriction e n a ha k w).val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t := by
  rw [rankStageGlobalCoreRestriction_val]
  change ((rankStageBoundaryIdeal (p := p) n k J).comap
    (rankStageCore e n a ha k).ι).subschemeι.appTop _ = _
  rw [IdealSheafClosedTransitions.section_square _ _ _ rfl, hw]
  change (IdealSheafClosedTransitions.map _ _ (rankStageCore e n a ha k).ι rfl ≫
    rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t = _
  rw [rankStageCoreBoundary_full_map]
  rfl

/-- The constructed correction vanishes on the entire original boundary at each order. -/
theorem rankStageGlobalBoundaryCoreCorrection_boundary (J : A.IdealSheafData)
    (v : rankStageCompatibleCoreInvariants e n a ha) (w : rankStageCompatibleInvariants e n)
    (t : Γ(J.subscheme, ⊤))
    (hv : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (v.val k).val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t)
    (hw : ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (w.val k).val =
      (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t) (k : ℕ) :
    (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
      ((rankStageGlobalBoundaryCoreCorrection e n a ha v w).val k).val = 0 := by
  change (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
    ((v.val k).val - (rankStageGlobalCoreRestriction e n a ha k (w.val k)).val) = 0
  rw [map_sub, hv k, rankStageGlobalCoreRestriction_boundary e n a ha J k _ t (hw k),
    sub_self]

variable (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)

/-- Refining a restricted global coefficient is the direct global restriction. -/
theorem rankStageGlobalCoreRestriction_refine (k : ℕ)
    (h : rankStageCore e n b hb k ≤ rankStageCore e n a ha k)
    (w : rankStageInvariants e n k) :
    rankStageCoreRefinement e n a b ha hb k h (rankStageGlobalCoreRestriction e n a ha k w) =
      rankStageGlobalCoreRestriction e n b hb k w := by
  apply Subtype.ext
  rw [rankStageCoreRefinement_val, rankStageGlobalCoreRestriction_val,
    rankStageGlobalCoreRestriction_val]
  change ((rankThickening (Over.mk p) n k).homOfLE h ≫
    (rankStageCore e n a ha k).ι).appTop w.val = _
  rw [Scheme.homOfLE_ι]

/-- Restriction of one global coefficient has zero full overlap error on arbitrary cores. -/
theorem rankStageGlobalCoreRestriction_overlap_zero (k : ℕ) (w : rankStageInvariants e n k) :
    rankStageInvariantOverlapError e n a b ha hb k
      (rankStageGlobalCoreRestriction e n a ha k w)
      (rankStageGlobalCoreRestriction e n b hb k w) = 0 := by
  simp only [rankStageInvariantOverlapError, rankStageGlobalCoreRestriction_refine, sub_self]

/-- The homogeneous correction cochain has exactly the original full overlap cocycle. -/
theorem rankStageGlobalBoundaryCoreCorrection_overlap
    (u : rankStageCompatibleCoreInvariants e n a ha)
    (v : rankStageCompatibleCoreInvariants e n b hb)
    (w : rankStageCompatibleInvariants e n) (k : ℕ) :
    rankStageInvariantOverlapError e n a b ha hb k
        ((rankStageGlobalBoundaryCoreCorrection e n a ha u w).val k)
        ((rankStageGlobalBoundaryCoreCorrection e n b hb v w).val k) =
      rankStageInvariantOverlapError e n a b ha hb k (u.val k) (v.val k) := by
  change rankStageInvariantOverlapError e n a b ha hb k
    (u.val k - rankStageGlobalCoreRestriction e n a ha k (w.val k))
    (v.val k - rankStageGlobalCoreRestriction e n b hb k (w.val k)) = _
  simp only [rankStageInvariantOverlapError, map_sub, rankStageGlobalCoreRestriction_refine]
  abel

end FLT.Mazur.EquivalenceRelationOrderedFrames
