/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeAdjacent
public import FLT.Mazur.WeierstrassDividedNonadjacentGlobalIntersection

/-!
# Nonadjacent exclusions in the fixed-stage node family

The original reversed atlas indices give full chart disjointness. Together
with the adjacent exclusion this separates nodes at every two different depths.
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

include D in
/-- Nonadjacent fixed-stage charts have exactly the original disjoint global images. -/
theorem retainedTensorChartAt_nonadjacent_disjoint (t : ℕ) (ht : t ≤ n)
    (a b : ℕ) (hab : a + 2 ≤ b) (hb : b + 1 ≤ t) :
    Disjoint (Set.range (retainedTensorChartAt hπ data t ht a (by omega)))
      (Set.range (retainedTensorChartAt hπ data t ht b hb)) := by
  obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, t = j + 2 + r := ⟨t - (j + 2), by omega⟩
  rw [retainedTensorChartAt_range_index, retainedTensorChartAt_range_index]
  have hp : algebraMap R K π = 0 := by
    exact (residue_eq_zero_iff π).mpr
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  have H := nonadjacentGlobalTensorAtlas_disjoint hπ data K j (by omega)
    (by omega) r ht ⟨j - a - 1, by omega⟩ hp
  have ha : (⟨j + 2 + r - a + 1, by omega⟩ : Fin (j + 2 + r + 3)) =
      Fin.succ ⟨(j - a - 1) + 2 + r + 1, by omega⟩ := Fin.ext (by dsimp; omega)
  have hb' : (⟨j + 2 + r - (j + 1) + 1, by omega⟩ : Fin (j + 2 + r + 3)) =
      Fin.succ ⟨r + 1, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [ha, hb']
  exact H

/-- A retained node misses every later retained chart, at adjacent or greater distance. -/
theorem retainedNodeSectionAt_later_disjoint (t : ℕ) (ht : t ≤ n)
    (a b : ℕ) (hab : a < b) (hb : b + 1 ≤ t)
    (hk : 2 * (start + a + 1) ≤ depth) (i : Fin 2) :
    Disjoint (Set.range (retainedNodeSectionAt hπ data D t ht a (by omega) hk i))
      (Set.range (retainedTensorChartAt hπ data t ht b hb)) := by
  by_cases h : b = a + 1
  · subst b
    exact retainedNodeSectionAt_next_disjoint hπ data D t ht a (by omega) hk i
  · exact (retainedTensorChartAt_nonadjacent_disjoint hπ data D t ht a b
      (by omega) hb).mono_left
      (retainedNodeSectionAt_range hπ data D t ht a (by omega) hk i)

/-- Every two different retained depths have disjoint node images in the final family. -/
theorem finalNodeSection_levels_disjoint (s : ℕ) (hs : s + 1 ≤ n)
    (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
    (a b : Fin (s + 1)) (hab : a < b) (i k : Fin 2) :
    Disjoint (Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (a, i)))))
      (Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (b, k))))) :=
  (retainedNodeSectionAt_later_disjoint hπ data D (s + 1) hs a.val b.val hab
    (by omega) (by omega) i).mono_right
      (retainedNodeSectionAt_range hπ data D (s + 1) hs b.val (by omega) (by omega) k)

end FLT.Mazur.WeierstrassDividedDepth
