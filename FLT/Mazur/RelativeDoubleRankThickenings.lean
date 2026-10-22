/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankThickeningFinite

/-!
# Independent endpoint rank thickenings

Successive ideal-power rank restrictions retain both original endpoints.
Their ranks are independent. Every point lifts at every pair of orders,
and both whole sources become finite without an original relation arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (n m r s : ℕ)

/-- Restrict the second endpoint on the full first endpoint rank thickening. -/
def doubleRankThickening : Scheme :=
  rankPullbackThickening E (rankPullbackMap E x n r ≫ y) m s

/-- The unchanged coefficient projection of the iterated rank restriction. -/
def doubleRankMap : doubleRankThickening E x y n m r s ⟶ B :=
  rankPullbackMap E (rankPullbackMap E x n r ≫ y) m s ≫ rankPullbackMap E x n r

/-- Both exact endpoint ranks hold on the entire iterated thickening. -/
theorem doubleRankMap_endpoints (z : doubleRankThickening E x y n m r s) :
    x (doubleRankMap E x y n m r s z) ∈ exactRank E n ∧
      y (doubleRankMap E x y n m r s z) ∈ exactRank E m := by
  exact ⟨rankPullback_endpoint E x n r _,
    rankPullback_endpoint E (rankPullbackMap E x n r ≫ y) m s z⟩

/-- The image is the intersection of the two independent exact rank pieces. -/
theorem doubleRankMap_range :
    Set.range (doubleRankMap E x y n m r s) =
      x ⁻¹' exactRank E n ∩ y ⁻¹' exactRank E m := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact doubleRankMap_endpoints E x y n m r s z
  · intro z hz
    have hu : z ∈ Set.range (rankPullbackMap E x n r) := by
      rw [rankPullbackMap_range]
      exact hz.1
    obtain ⟨u, hu⟩ := hu
    have hv : u ∈ Set.range (rankPullbackMap E (rankPullbackMap E x n r ≫ y) m s) := by
      rw [rankPullbackMap_range]
      change y (rankPullbackMap E x n r u) ∈ exactRank E m
      rw [hu]
      exact hz.2
    obtain ⟨v, hv⟩ := hv
    exact ⟨v, (congrArg (rankPullbackMap E x n r) hv).trans hu⟩

variable [QuasiCompact E.hom]

/-- All original points are covered at every pair of infinitesimal orders. -/
theorem exists_doubleRank_lift (z : B) :
    ∃ (n m : ℕ) (w : doubleRankThickening E x y n m r s),
      doubleRankMap E x y n m r s w = z := by
  obtain ⟨n, hn⟩ := exists_exactRank E (x z)
  obtain ⟨m, hm⟩ := exists_exactRank E (y z)
  have hw : z ∈ Set.range (doubleRankMap E x y n m r s) := by
    rw [doubleRankMap_range]
    exact ⟨hn, hm⟩
  obtain ⟨w, hw⟩ := hw
  exact ⟨n, m, w, hw⟩

/-- A geometric uniform rank bound bounds both indices of the covering stages. -/
theorem exists_bounded_doubleRank_lifts [TopologicalSpace.NoetherianSpace S] :
    ∃ N : ℕ, ∀ z : B, ∃ (n m : ℕ), n ≤ N ∧ m ≤ N ∧
      ∃ w : doubleRankThickening E x y n m r s, doubleRankMap E x y n m r s w = z := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  refine ⟨N, fun z ↦ ?_⟩
  obtain ⟨n, m, w, hw⟩ := exists_doubleRank_lift E x y r s z
  obtain ⟨hx, hy⟩ := doubleRankMap_endpoints E x y n m r s w
  exact ⟨n, m, hN _ n hx.1, hN _ m hy.1, w, hw⟩

variable [LocallyQuasiFinite E.hom]

/-- Both entire original sources are finite over each full two-rank stage. -/
theorem doubleRank_both_sources_finite :
    IsFinite (pullback.snd E.hom (doubleRankMap E x y n m r s ≫ x)) ∧
      IsFinite (pullback.snd E.hom (doubleRankMap E x y n m r s ≫ y)) := by
  constructor
  · apply finite_pullback_of_exactRank E n
    rintro _ ⟨z, rfl⟩
    exact (doubleRankMap_endpoints E x y n m r s z).1
  · apply finite_pullback_of_exactRank E m
    rintro _ ⟨z, rfl⟩
    exact (doubleRankMap_endpoints E x y n m r s z).2

end FLT.Mazur.RelativeOrderedTuples
