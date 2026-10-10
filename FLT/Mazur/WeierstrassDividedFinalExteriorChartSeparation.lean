/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedZeroExteriorLine
public import FLT.Mazur.WeierstrassDividedFinalZeroExteriorRanges
public import FLT.Mazur.WeierstrassDividedAdjacentPairIntersections

/-!
# The complete exterior excludes all later retained charts

Both its full incidence line and unchanged infinity chart are included.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "E" => finalZeroExteriorComponent hπ data D s hs hstart hk

/-- The complete exterior is exactly its original full line and infinity chart. -/
theorem finalZeroExteriorComponent_range_line_infinity :
    Set.range E =
      Set.range (retainedZeroExteriorLineAt hπ data D (s + 1) hs 0
        (by omega) (by omega) (by omega)) ∪
      Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) := by
  rw [finalZeroExteriorComponent, infinity_chart_comp_range,
    zeroRetainedOrientedToGlobal_range, zeroRetainedExteriorToGlobal_range, Set.image_union,
    ← infinity_chart_comp_range, ← infinity_chart_comp_range]
  rw [← retainedZeroExteriorLineAt_original hπ data D 0 (by omega) s (by omega),
    retainedZeroExteriorLineAt_index_transport hπ data D _ hs (by omega),
    finiteInfinityTensorChart_index_transport hπ data _ hs (by omega)]

/-- Every strictly later retained chart is disjoint from the entire complete exterior. -/
theorem finalZeroExteriorComponent_later_chart_disjoint (j : ℕ)
    (hj : 0 < j) (hjs : j ≤ s) :
    Disjoint (Set.range E)
      (Set.range (retainedTensorChartAt hπ data (s + 1) hs j (by omega))) := by
  rw [finalZeroExteriorComponent_range_line_infinity]
  exact Set.disjoint_union_left.mpr
    ⟨retainedZeroExteriorLineAt_later_disjoint hπ data D (s + 1) hs 0 j hj
      (by omega) (by omega) (by omega),
    (retainedTensorChartAt_infinity_disjoint hπ data D (s + 1) hs j
      (by omega) (by omega)).symm⟩

/-- The exterior misses both complete adjacent components at every positive chain level. -/
theorem finalZeroExteriorComponent_later_adjacent_disjoint (j : Fin s)
    (hj : 0 < j.val) (i : Fin 2) :
    Disjoint (Set.range E)
      (Set.range (finalAdjacentComponent hπ data D s hs hk j i)) := by
  rw [finalAdjacentComponent_range_line_node]
  exact Set.disjoint_union_right.mpr
    ⟨(finalZeroExteriorComponent_later_chart_disjoint hπ data D s hs hstart hk
      (j.val + 1) (by omega) (by omega)).mono_right
      (retainedLineAt_range hπ data D (s + 1) hs (j.val + 1)
        (by omega) (by omega) (by omega) i),
    (finalZeroExteriorComponent_later_chart_disjoint hπ data D s hs hstart hk
      j.val hj (by omega)).mono_right
      (retainedNodeSectionAt_range hπ data D (s + 1) hs j.val (by omega) (by omega) i)⟩

/-- Each original initial retained node lies on the complete exterior. -/
theorem finalZeroExteriorComponent_initial_node_subset
    (hp : 2 * (start + s + 1) < depth) (i : Fin 2) :
    Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (0, i)))) ⊆
      Set.range E := by
  fin_cases i
  · change Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (0, 0)))) ⊆ _
    rw [← finalZeroExteriorComponent_zero hπ data D s hs hstart hk hp]
    exact componentRange_comp_subset _ _
  · change Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (0, 1)))) ⊆ _
    rw [← finalZeroExteriorComponent_infinity hπ data D s hs hstart hk hp]
    exact componentRange_comp_subset _ _

/-- At positive length each first component meets the exterior exactly at its initial node. -/
theorem finalZeroExteriorComponent_first_adjacent_inter (hs0 : 0 < s)
    (hp : 2 * (start + s + 1) < depth) (i : Fin 2) :
    Set.range E ∩
        Set.range (finalAdjacentComponent hπ data D s hs hk ⟨0, hs0⟩ i) =
      Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (0, i)))) := by
  rw [finalAdjacentComponent_range_line_node]
  have hd := (finalZeroExteriorComponent_later_chart_disjoint hπ data D s hs hstart hk
    1 (by omega) (by omega)).mono_right
    (retainedLineAt_range hπ data D (s + 1) hs 1 (by omega) (by omega) (by omega) i)
  have hn := finalZeroExteriorComponent_initial_node_subset hπ data D s hs hstart hk hp i
  ext z
  constructor
  · rintro ⟨hz, hl | hn⟩
    · exact (Set.disjoint_left.mp hd hz hl).elim
    · exact hn
  · intro hz
    exact ⟨hn hz, Or.inr hz⟩

end FLT.Mazur.WeierstrassDividedDepth
