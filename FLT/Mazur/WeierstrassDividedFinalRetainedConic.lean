/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeChart
public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroConic

/-!
# The entire retained conic in a fixed final stage

The same original conic is retained at every later stage, with the positive-scale
and scale-one immersions selected by the actual starting depth.
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

open WeierstrassModificationX

/-- The entire original conic, including both full parameter charts. -/
def orderedRetainedConic (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
    (hk : 2 * (start + j + 1) ≤ depth) :=
  if h : 0 < start + j then olderGlobalMiddleConic hπ data D j hj r hr h hk
  else olderGlobalZeroConic hπ data D j hj r hr (by omega) hk

/-- At positive scale the uniform conic is the original middle conic. -/
theorem orderedRetainedConic_positive (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk : 2 * (start + j + 1) ≤ depth)
    (h : 0 < start + j) :
    orderedRetainedConic hπ data D j hj r hr hk =
      olderGlobalMiddleConic hπ data D j hj r hr h hk := by
  simp only [orderedRetainedConic, dite_eq_left h]

/-- At scale one the uniform conic is the original first conic. -/
theorem orderedRetainedConic_zero (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk : 2 * (start + j + 1) ≤ depth)
    (h : start + j = 0) :
    orderedRetainedConic hπ data D j hj r hr hk =
      olderGlobalZeroConic hπ data D j hj r hr h hk := by
  simp only [orderedRetainedConic, dite_eq_right (show ¬0 < start + j by omega)]

/-- The original conic with only its target stage index rewritten. -/
def retainedConicAt (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk : 2 * (start + j + 1) ≤ depth) :=
  orderedRetainedConic hπ data D j (by omega) (t - (j + 1)) (by omega) hk ≫
    eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) ht (by omega))

/-- The fixed-stage conic recovers the entire original retained conic. -/
theorem retainedConicAt_original (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk : 2 * (start + j + 1) ≤ depth) :
    retainedConicAt hπ data D (j + 1 + r) hr j (by omega) hk =
      orderedRetainedConic hπ data D j hj r hr hk := by
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans ?_
  congr 1
  · omega
  · apply proof_irrel_heq

/-- Index transport of the target preserves the complete retained conic map. -/
@[reassoc] theorem retainedConicAt_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (j : ℕ) (hj : j + 1 ≤ a) (hk : 2 * (start + j + 1) ≤ depth) :
    retainedConicAt hπ data D a ha j hj hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      retainedConicAt hπ data D b hb j (by omega) hk := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- The adjacent-stage spelling changes only the target index of the full conic. -/
theorem retainedConicAt_adjacent_original (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 2 + r ≤ n) (hk : 2 * (start + j + 1) ≤ depth) :
    retainedConicAt hπ data D (j + 2 + r) hr j (by omega) hk =
      orderedRetainedConic hπ data D j hj (r + 1) (by omega) hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr
          (show j + 1 + (r + 1) = j + 2 + r by omega)) := by
  rw [← retainedConicAt_original hπ data D j hj (r + 1) (by omega) hk,
    retainedConicAt_index_transport hπ data D _ hr (by omega)]

/-- The conic remains inside its full original containing chart. -/
theorem retainedConicAt_range_subset_chart (t : ℕ) (ht : t ≤ n)
    (j : ℕ) (hj : j + 1 ≤ t) (hk : 2 * (start + j + 1) ≤ depth) :
    Set.range (retainedConicAt hπ data D t ht j hj hk) ⊆
      Set.range (retainedTensorChartAt hπ data t ht j hj) := by
  obtain ⟨r, he⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedConicAt_original hπ data D j (by omega),
    retainedTensorChartAt_original hπ data j (by omega)]
  by_cases h : 0 < start + j
  · rw [orderedRetainedConic_positive hπ data D j (by omega) r ht hk h]
    exact Set.Subset.trans (Set.subset_union_left)
      (le_of_eq (olderGlobalMiddleComponents_cover hπ data D j (by omega) r ht h hk))
  · rw [orderedRetainedConic_zero hπ data D j (by omega) r ht hk (by omega)]
    exact Set.Subset.trans (Set.subset_union_right)
      (le_of_eq (olderGlobalZeroComponents_cover hπ data D j (by omega) r ht (by omega) hk))

end FLT.Mazur.WeierstrassDividedDepth
