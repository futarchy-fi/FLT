/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankThickenings
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Finite-order recovery on two independent exact ranks

Every compact coefficient test of two fixed ranks factors through some pair
of original infinitesimal orders. A compact coefficient scheme of those ranks
is recovered by an isomorphism, with its entire structure sheaf retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B T : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (n m : ℕ)

instance doubleRankMap_mono (r s : ℕ) : Mono (doubleRankMap E x y n m r s) := by
  unfold doubleRankMap
  infer_instance

variable [IsNoetherian S]

/-- Both independent exact ranks give finite-order factorization of the full compact test. -/
theorem exists_doubleRank_factor [CompactSpace T] (v : T ⟶ B)
    (hx : Set.range (v ≫ x) ⊆ exactRank E n)
    (hy : Set.range (v ≫ y) ⊆ exactRank E m) :
    ∃ (r s : ℕ) (g : T ⟶ doubleRankThickening E x y n m r s),
      g ≫ doubleRankMap E x y n m r s = v := by
  obtain ⟨r, a, ha⟩ := exists_rankPullback_factor E n x v hx
  have hb : Set.range (a ≫ rankPullbackMap E x n r ≫ y) ⊆ exactRank E m := by
    rwa [← Category.assoc, ha]
  obtain ⟨s, b, hb⟩ :=
    exists_rankPullback_factor E m (rankPullbackMap E x n r ≫ y) a hb
  refine ⟨r, s, b, ?_⟩
  change b ≫ rankPullbackMap E (rankPullbackMap E x n r ≫ y) m s ≫
    rankPullbackMap E x n r = v
  rw [← Category.assoc, hb, ha]

/-- Both pointwise rank conditions are equivalent to full finite-order factorization. -/
theorem exactRanks_iff_doubleRank_factor [CompactSpace T] (v : T ⟶ B) :
    (Set.range (v ≫ x) ⊆ exactRank E n ∧ Set.range (v ≫ y) ⊆ exactRank E m) ↔
      ∃ (r s : ℕ) (g : T ⟶ doubleRankThickening E x y n m r s),
        g ≫ doubleRankMap E x y n m r s = v := by
  refine ⟨fun h ↦ exists_doubleRank_factor E x y n m v h.1 h.2, ?_⟩
  rintro ⟨r, s, g, rfl⟩
  constructor
  · rintro _ ⟨z, rfl⟩
    exact (doubleRankMap_endpoints E x y n m r s (g z)).1
  · rintro _ ⟨z, rfl⟩
    exact (doubleRankMap_endpoints E x y n m r s (g z)).2

/-- A compact two-rank coefficient scheme is recovered whole at some finite pair of orders. -/
theorem exists_doubleRankMap_isIso [CompactSpace B]
    (hx : Set.range x ⊆ exactRank E n) (hy : Set.range y ⊆ exactRank E m) :
    ∃ r s : ℕ, IsIso (doubleRankMap E x y n m r s) := by
  obtain ⟨r, s, g, hg⟩ := exists_doubleRank_factor E x y n m (𝟙 B)
    (by simpa using hx) (by simpa using hy)
  refine ⟨r, s, ⟨g, ?_, hg⟩⟩
  apply (cancel_mono (doubleRankMap E x y n m r s)).mp
  rw [Category.assoc, hg, Category.comp_id, Category.id_comp]

end FLT.Mazur.RelativeOrderedTuples
