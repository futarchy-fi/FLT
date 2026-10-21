/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstructibleImageGenerizations
public import FLT.Mazur.RelativeRankCollisionFinite

/-!
# Constructible compactness of the actual unequal-rank locus

The geometric base supplies compact rank opens and a finite rank bound.
Quasi-compact endpoint maps pull these back to compact opens on the test
scheme. Finite Boolean operations make the entire collision set closed in
the constructible topology, without Noetherianity of the test or scalar ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  [NoetherianSpace A] (x y : T ⟶ A) [QuasiCompact x] [QuasiCompact y]

/-- Exact rank on a quasi-compact endpoint is clopen in the constructible topology. -/
theorem exactRank_preimage_constructible_clopen (n : ℕ) :
    IsClopen[constructibleTopology T] (x ⁻¹' exactRank E n) := by
  have h (m : ℕ) : IsClopen[constructibleTopology T]
      (x ⁻¹' (rankImageOpen E m : Set A)) :=
    (x.isSpectralMap.isCompact_preimage_of_isOpen (rankImageOpen E m).isOpen
      (NoetherianSpace.isCompact _)).isClopen_constructibleTopology_of_isOpen
        ((rankImageOpen E m).isOpen.preimage x.continuous)
  change IsClopen[constructibleTopology T]
    ((x ⁻¹' (rankImageOpen E n : Set A)) ∩
      (x ⁻¹' (rankImageOpen E (n + 1) : Set A))ᶜ)
  let _ : TopologicalSpace T := constructibleTopology T
  exact (h n).inter (h (n + 1)).compl

/-- Each actual rank-pair locus is constructibly closed, including the empty diagonal cases. -/
theorem rankPairLocus_constructibly_closed (n m : ℕ) :
    IsClosed[constructibleTopology T] (rankPairLocus E x y n m) := by
  by_cases h : n = m
  · simp only [rankPairLocus, h, ne_eq, not_true_eq_false, false_and, Set.ofPred_false]
    exact @isClosed_empty T (constructibleTopology T)
  · have he : rankPairLocus E x y n m =
        x ⁻¹' exactRank E n ∩ y ⁻¹' exactRank E m := by
      ext t
      exact ⟨fun ht ↦ ht.2, fun ht ↦ ⟨h, ht⟩⟩
    rw [he]
    have hx := exactRank_preimage_constructible_clopen E x n
    have hy := exactRank_preimage_constructible_clopen E y m
    let _ : TopologicalSpace T := constructibleTopology T
    exact hx.1.inter hy.1

variable [QuasiCompact E.hom]

/-- The finite geometric rank bound makes all collisions constructibly closed at once. -/
theorem rankCollision_constructibly_closed :
    IsClosed[constructibleTopology T] (rankCollision E x y) := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  rw [rankCollision_eq_finite_union E x y N hN]
  have h := rankPairLocus_constructibly_closed E x y
  let _ : TopologicalSpace T := constructibleTopology T
  exact isClosed_iUnion_of_finite fun n ↦ isClosed_iUnion_of_finite fun m ↦ h n.val m.val

/-- A qcqs test scheme makes the full actual collision set constructibly compact. -/
theorem rankCollision_constructibly_compact [CompactSpace T] [QuasiSeparatedSpace T] :
    @IsCompact T (constructibleTopology T) (rankCollision E x y) :=
  ConstructibleImageGenerizations.compact_of_constructibly_closed
    (rankCollision_constructibly_closed E x y)

end FLT.Mazur.RelativeOrderedTuples
