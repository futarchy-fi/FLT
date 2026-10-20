/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankOpenHomogeneousAlgebraization

/-!
# Simultaneous homogeneous algebraization on a top rank open

A family of ordinary compatible homogeneous towers has original rank-open
representatives. Equations may be checked at every order without expanding
the geometry of the individual towers in the algebraization proof.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [CompactSpace A]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance familyOpenOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance familyOpenOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance familyOpenOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (hn : rankImageOpen (Over.mk p) (n + 1) = ⊥)
  (J : A.IdealSheafData) {ι : Type*}
local notation "B" => J.comap (Scheme.Opens.ι (rankImageOpen (Over.mk p) n))
local notation "R" => compatibleFunctions (rankOpenFirst (p := p) n) (rankOpenSecond e n)
attribute [local irreducible] rankImageOpen rankOpenFirst rankOpenSecond
  rankStageGlobalBoundaryKernel rankStageInvariantTransition

include hn in
/-- Simultaneous algebraization preserves every full original boundary equation. -/
theorem exists_rankOpen_homogeneous_family
    (w : ∀ _ : ι, ∀ k, rankStageInvariants e n k)
    (hb : ∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k)
    (ht : ∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) :
    ∃ z : ι → R, (∀ j, (B).subschemeι.appTop (z j).val = 0) ∧
      ∀ j k, rankOpenInvariantRestriction e n k (z j) = w j k := by
  have hz (j : ι) := exists_rankOpen_homogeneous_of_next_empty e n J hn
    (⟨w j, ht j⟩ : rankStageCompatibleInvariants e n) (hb j)
  choose z hzB hzW using hz
  refine ⟨z, hzB, fun j k ↦ ?_⟩
  exact congrArg (fun v : rankStageCompatibleInvariants e n ↦ v.val k) (hzW j)

end FLT.Mazur.EquivalenceRelationOrderedFrames
