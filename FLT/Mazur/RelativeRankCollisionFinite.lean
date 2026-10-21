/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankCollisionIdeal

/-!
# Finite geometric detection of the scalar rank obstruction

Noetherianity of the original geometric base gives a finite rank bound.
Consequently the collision ideal is a finite intersection of the scalar
vanishing ideals of actual rank-pair loci. This does not assert that any
of these scalar ideals is finitely generated.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (x y : T ⟶ A)

/-- The original locally closed locus for one ordered pair of unequal ranks. -/
def rankPairLocus (n m : ℕ) : Set T :=
  {t | n ≠ m ∧ x t ∈ exactRank E n ∧ y t ∈ exactRank E m}

omit [QuasiCompact E.hom] in
/-- Each individual rank-pair test is locally closed in the actual test scheme. -/
theorem rankPairLocus_isLocallyClosed (n m : ℕ) :
    IsLocallyClosed (rankPairLocus E x y n m) := by
  by_cases h : n = m
  · simp only [rankPairLocus, h, ne_eq, not_true_eq_false, false_and, Set.ofPred_false]
    exact isClosed_empty.isLocallyClosed
  · have he : rankPairLocus E x y n m =
        x ⁻¹' exactRank E n ∩ y ⁻¹' exactRank E m := by
      ext t
      exact ⟨fun ht ↦ ht.2, fun ht ↦ ⟨h, ht⟩⟩
    rw [he]
    exact ((exactRank_isLocallyClosed E n).preimage x.continuous).inter
      ((exactRank_isLocallyClosed E m).preimage y.continuous)

omit [QuasiCompact E.hom] in
/-- A geometric rank bound decomposes all collisions into finitely many actual pair tests. -/
theorem rankCollision_eq_finite_union (N : ℕ)
    (hN : ∀ a : A, ∀ n : ℕ, a ∈ rankImageOpen E n → n ≤ N) :
    rankCollision E x y =
      ⋃ n : Fin (N + 1), ⋃ m : Fin (N + 1), rankPairLocus E x y n.val m.val := by
  ext t
  constructor
  · rintro ⟨n, m, hnm, hn, hm⟩
    exact Set.mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_of_le (hN _ _ hn.1)⟩,
      Set.mem_iUnion.mpr ⟨⟨m, Nat.lt_succ_of_le (hN _ _ hm.1)⟩, hnm, hn, hm⟩⟩
  · intro ht
    obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
    obtain ⟨m, ht⟩ := Set.mem_iUnion.mp ht
    exact ⟨n.val, m.val, ht⟩

variable {R : Type} [CommRing R] (s : T ⟶ Spec (.of R))

omit [QuasiCompact E.hom] in
/-- Only finitely many closed scalar images contribute to the complete obstruction. -/
theorem rankCollision_closure_finite (N : ℕ)
    (hN : ∀ a : A, ∀ n : ℕ, a ∈ rankImageOpen E n → n ≤ N) :
    closure (s '' rankCollision E x y) =
      ⋃ n : Fin (N + 1), ⋃ m : Fin (N + 1),
        closure (s '' rankPairLocus E x y n.val m.val) := by
  rw [rankCollision_eq_finite_union E x y N hN]
  simp only [Set.image_iUnion, closure_iUnion_of_finite]

/-- A geometric bound gives a finite ideal intersection without scalar finiteness. -/
theorem exists_rankCollisionIdeal_finite [NoetherianSpace A] :
    ∃ N : ℕ, rankCollisionIdeal E x y s =
      ⨅ n : Fin (N + 1), ⨅ m : Fin (N + 1),
        PrimeSpectrum.vanishingIdeal (s '' rankPairLocus E x y n.val m.val) := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  refine ⟨N, ?_⟩
  rw [rankCollisionIdeal, rankCollision_eq_finite_union E x y N hN]
  simp only [Set.image_iUnion, PrimeSpectrum.vanishingIdeal_iUnion]

end FLT.Mazur.RelativeOrderedTuples
