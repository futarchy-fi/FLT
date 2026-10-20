/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoherentAffineCores

/-!
# Exact affine intersections of coherent original cores

Multiplying original parameters constructs the intersection core at every
order. In particular overlaps are affine and have the same exact transition
laws as the original cores, without a separatedness assumption on the ambient
rank stage or a replacement of the original relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationAffinePrincipalCore
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme} {p q : D ⟶ A} [IsFinite p] [Flat p]
  [LocallyOfFinitePresentation p] (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Products of principal parameters give exact intersections of whole-orbit cores. -/
theorem core_mul (a b : Γ(A, ⊤)) (ha : IsAffineOpen (A.basicOpen a))
    (hb : IsAffineOpen (A.basicOpen b)) (hab : IsAffineOpen (A.basicOpen (a * b))) :
    core (p := p) (q := q) (a * b) hab =
      core (p := p) (q := q) a ha ⊓ core (p := p) (q := q) b hb := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  change x ∈ core (p := p) (q := q) (a * b) hab ↔
    x ∈ core (p := p) (q := q) a ha ∧ x ∈ core (p := p) (q := q) b hb
  rw [mem_core_iff e, mem_core_iff e, mem_core_iff e, Scheme.basicOpen_mul]
  exact ⟨fun h ↦ ⟨fun z hz ↦ (h z hz).1, fun z hz ↦ (h z hz).2⟩,
    fun h z hz ↦ ⟨h.1 z hz, h.2 z hz⟩⟩

end FLT.Mazur.FiniteRelationAffinePrincipalCore

namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance intersectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance intersectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance intersectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a b : Γ(A, ⊤))
  (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)

omit [QuasiCompact p] [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p] in
include ha in
/-- The product remains an original parameter in the same rank open. -/
theorem rankStageProduct_domain : A.basicOpen (a * b) ≤ rankImageOpen (Over.mk p) n := by
  rw [Scheme.basicOpen_mul]
  exact inf_le_left.trans ha

/-- Two named cores meet in the named core of their original product parameter. -/
theorem rankStageCore_mul (k : ℕ) :
    rankStageCore e n (a * b) (rankStageProduct_domain n a b ha) k =
      rankStageCore e n a ha k ⊓ rankStageCore e n b hb k := by
  let _ := rankStageFirst_finite (p := p) n k
  unfold rankStageCore
  simp only [map_mul]
  exact FiniteRelationAffinePrincipalCore.core_mul (rankStageEquivalence e n k) _ _ _ _ _

/-- Every cross-core overlap is affine, including all its nilpotents. -/
theorem rankStageCore_intersection_affine (k : ℕ) :
    IsAffineOpen (rankStageCore e n a ha k ⊓ rankStageCore e n b hb k) := by
  rw [← rankStageCore_mul e n a b ha hb]
  exact rankStageCore_affine e n (a * b) (rankStageProduct_domain n a b ha) k

end FLT.Mazur.EquivalenceRelationOrderedFrames
