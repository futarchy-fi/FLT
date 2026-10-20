/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageAffineNeighborhoods
public import FLT.Mazur.RankStageBoundaryIdeal
public import FLT.Mazur.FiniteEtaleInvariantOpenBoundary

/-!
# Actual invariant boundary lifts on every infinitesimal rank stage

Each original point has a rank-stage affine neighborhood where the full
boundary invariant restriction is surjective. These are sections on the whole
restricted stage relation, with the original boundary equations intact.
Descent across the nonflat stage maps is a separate problem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance rankLiftOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankLiftOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankLiftOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable [IsAffine S] (f : A ⟶ S) (h : p ≫ f = q ≫ f) [IsSeparated f]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q) (n k : ℕ)
local notation "b" => rankThickeningMap (Over.mk p) n k
local notation "r" => rankStageFirst (p := p) n k
local notation "s" => rankStageSecond e n k
local notation "I" => rankStageBoundaryIdeal (p := p) n k J
local notation "hI" => rankStageBoundaryIdeal_invariant e n k J hJ

include h in
/-- The actual full boundary invariant map is surjective on every affine invariant stage domain. -/
theorem rankStage_boundaryRestriction_surjective
    (U : (rankThickening (Over.mk p) n k).Opens) (hU : r ⁻¹ᵁ U = s ⁻¹ᵁ U)
    (ha : IsAffineOpen U) :
    Function.Surjective (FiniteEtaleInvariantOpenBoundary.restriction r s U hU I hI) := by
  let _ := rankStageFirst_finite (p := p) n k
  let _ : IsSeparated (b ≫ f) := by
    unfold rankThickeningMap
    infer_instance
  have hf : r ≫ (b ≫ f) = s ≫ (b ≫ f) := by
    rw [← Category.assoc, ← (rankStageFirst_isPullback (p := p) n k).w,
      Category.assoc, h, ← Category.assoc, ← rankStageSecond_map, Category.assoc]
  exact FiniteEtaleInvariantOpenBoundary.restriction_surjective r s U hU I hI
    (b ≫ f) hf (rankStageEquivalence e n k) ha

include h in
/-- All original points have full-relation boundary lifting neighborhoods on every stage order. -/
theorem exists_rankStage_boundary_lifting_neighborhood [IsAffine A] (x : A) :
    ∃ (m : ℕ) (y : rankThickening (Over.mk p) m k)
      (U : (rankThickening (Over.mk p) m k).Opens)
      (hU : rankStageFirst (p := p) m k ⁻¹ᵁ U = rankStageSecond e m k ⁻¹ᵁ U),
      rankThickeningMap (Over.mk p) m k y = x ∧ IsAffineOpen U ∧ y ∈ U ∧
      Function.Surjective (FiniteEtaleInvariantOpenBoundary.restriction
        (rankStageFirst (p := p) m k) (rankStageSecond e m k) U hU
        (rankStageBoundaryIdeal (p := p) m k J)
        (rankStageBoundaryIdeal_invariant e m k J hJ)) := by
  obtain ⟨m, y, U, hy, ha, hyU, hU⟩ := exists_rankStage_affine_lift e k x
  exact ⟨m, y, U, hU, hy, ha, hyU,
    rankStage_boundaryRestriction_surjective e f h J hJ m k U hU ha⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
