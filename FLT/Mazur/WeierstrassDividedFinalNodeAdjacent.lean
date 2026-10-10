/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeChart

/-!
# Adjacent exclusions in the fixed-stage node family

The full positive-depth and scale-one exclusions are transported without changing
any node section, tangent ordering, or original chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Numerical stage transport preserves the original retained section as a dependent map. -/
theorem retainedNodeSectionAt_heq (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (r : ℕ) (hr : j + 1 + r ≤ n) (he : j + 1 + r = t)
    (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    HEq (retainedNodeSectionAt hπ data D t ht j hj hk i)
      (orderedRetainedSection hπ data D j (by omega) r hr hk i) := by
  subst t
  rw [retainedNodeSectionAt_original hπ data D j (by omega) r hr hk i]

/-- Each retained ordered node misses the entire adjacent next chart in the fixed model. -/
theorem retainedNodeSectionAt_next_disjoint (t : ℕ) (ht : t ≤ n)
    (j : ℕ) (hj : j + 2 ≤ t) (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    Disjoint (Set.range (retainedNodeSectionAt hπ data D t ht j (by omega) hk i))
      (Set.range (retainedTensorChartAt hπ data t ht (j + 1) (by omega))) := by
  obtain ⟨r, he⟩ : ∃ r, t = j + 2 + r := ⟨t - (j + 2), by omega⟩
  subst t
  rw [retainedTensorChartAt_original hπ data (j + 1) (by omega) r ht]
  have H := retainedNodeSectionAt_heq hπ data D (j + 2 + r) ht j (by omega)
    (r + 1) (by omega) (by omega) hk i
  by_cases h : 0 < start + j
  · rw [orderedRetainedSection_positive hπ data D j (by omega) (r + 1)
      (by omega) hk h] at H
    fin_cases i
    · have e := eq_of_heq (H.trans
        (adjacentRetainedFirstSection_original hπ data D j (by omega) h hk r ht))
      rw [e]
      exact adjacentRetainedFirstSection_next_disjoint hπ data D j (by omega)
        h hk (by omega) r ht
    · have e := eq_of_heq (H.trans
        (adjacentRetainedSecondSection_original hπ data D j (by omega) h hk r ht))
      rw [e]
      exact adjacentRetainedSecondSection_next_disjoint hπ data D j (by omega)
        h hk (by omega) r ht
  · rw [orderedRetainedSection_zero hπ data D j (by omega) (r + 1)
      (by omega) hk (by omega)] at H
    fin_cases i
    · have e := eq_of_heq (H.trans
        (adjacentZeroFirstSection_original hπ data D j (by omega) (by omega) hk r ht))
      rw [e]
      exact adjacentZeroFirstSection_next_disjoint hπ data D j (by omega)
        (by omega) hk (by omega) r ht
    · have e := eq_of_heq (H.trans
        (adjacentZeroSecondSection_original hπ data D j (by omega) (by omega) hk r ht))
      rw [e]
      exact adjacentZeroSecondSection_next_disjoint hπ data D j (by omega)
        (by omega) hk (by omega) r ht

/-- Adjacent levels of the final family have disjoint node images, in either order. -/
theorem finalNodeSection_adjacent_disjoint (s : ℕ) (hs : s + 1 ≤ n)
    (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
    (j : ℕ) (hj : j + 1 < s + 1) (a b : Fin 2) :
    Disjoint
      (Set.range (finalNodeSection hπ data D s hs hk hp
        (.inl (.inr (⟨j, by omega⟩, a)))))
      (Set.range (finalNodeSection hπ data D s hs hk hp
        (.inl (.inr (⟨j + 1, hj⟩, b))))) := by
  have H := (retainedNodeSectionAt_next_disjoint hπ data D (s + 1) hs j (by omega) (by omega) a)
  exact H.mono_right (retainedNodeSectionAt_range hπ data D (s + 1) hs (j + 1)
      (by omega) (by omega) b)

end FLT.Mazur.WeierstrassDividedDepth
