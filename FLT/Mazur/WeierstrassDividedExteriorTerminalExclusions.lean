/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapOpenExclusion
public import FLT.Mazur.WeierstrassDividedFinalExteriorChartSeparation
public import FLT.Mazur.WeierstrassDividedTerminalComponentExclusions
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodeBoundaries

/-!
# The exterior excludes the terminal node and all positive-level terminal components

The infinity chart cannot meet a projective component only at its omitted endpoint.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R

/-- At scale one the full left affine parameter is contained in the original conic. -/
theorem finalTerminalComponent_zero_left_range_conic (hzero : start + s = 0) (i : Fin 2) :
    Set.range (ProjectiveLine.left K ≫ finalTerminalComponent hπ data D s hs hk hp i) ⊆
      Set.range (olderGlobalZeroConic hπ data D s hs 0 hs hzero hk) := by
  rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp hzero]
  fin_cases i
  · change Set.range (ProjectiveLine.left K ≫
      terminalZeroFirstComponent hπ data D s hs hzero hk hp) ⊆ _
    rw [terminalZeroFirstComponent_left, terminalZeroConicFirstParameter_retained]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · change Set.range (ProjectiveLine.left K ≫
      terminalZeroSecondComponent hπ data D s hs hzero hk hp) ⊆ _
    rw [terminalZeroSecondComponent_left, terminalZeroConicSecondParameter_retained]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩

/-- Complete terminal components miss infinity, at both scale one and positive depth. -/
theorem finalTerminalComponent_infinity_chart_disjoint (i : Fin 2) :
    Disjoint (Set.range (finalTerminalComponent hπ data D s hs hk hp i))
      (Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs)) := by
  apply ProjectiveLine.map_range_open_disjoint_of_left K
  by_cases hpos : 0 < start + s
  · exact (retainedTensorChartAt_infinity_disjoint hπ data D (s + 1) hs s
      (by omega) hpos).mono_left
      (finalTerminalComponent_left_range_chart hπ data D s hs hk hp hpos i)
  · have hzero : start + s = 0 := by omega
    have hc : Disjoint (Set.range (olderGlobalZeroConic hπ data D s hs 0 hs hzero hk))
        (Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs)) := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨x, rfl⟩ hx
      have H := olderGlobalZeroConic_infinity_preimage_empty hπ data D s hs 0 hs hzero hk
      exact (Set.ext_iff.mp H x).mp hx
    exact hc.mono_left
      (finalTerminalComponent_zero_left_range_conic hπ data D s hs hk hp hzero i)

/-- The terminal node also misses the original infinity chart. -/
theorem finalNodeSection_terminal_infinity_disjoint :
    Disjoint (Set.range (finalNodeSection hπ data D s hs hk hp (.inr ())))
      (Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs)) := by
  rw [← finalTerminalComponent_infinity hπ data D s hs hk hp 0]
  exact (finalTerminalComponent_infinity_chart_disjoint hπ data D s hs hk hp 0).mono_left
    (componentRange_comp_subset _ _)

variable (hstart : start = 0)

/-- The entire complete exterior excludes the original terminal node at every chain length. -/
theorem finalZeroExteriorComponent_terminal_node_disjoint :
    Disjoint (Set.range (finalZeroExteriorComponent hπ data D s hs hstart hk))
      (Set.range (finalNodeSection hπ data D s hs hk hp (.inr ()))) := by
  rw [finalZeroExteriorComponent_range_line_infinity]
  exact Set.disjoint_union_left.mpr
    ⟨((terminalNode_retainedTensorChart_disjoint hπ data D s hs hk hp 0 (by omega)).mono_right
      (retainedZeroExteriorLineAt_range hπ data D (s + 1) hs 0
        (by omega) (by omega) (by omega))).symm,
    (finalNodeSection_terminal_infinity_disjoint hπ data D s hs hk hp).symm⟩

/-- A positive chain length separates the exterior from both complete terminal components. -/
theorem finalZeroExteriorComponent_later_terminal_disjoint (hs0 : 0 < s) (i : Fin 2) :
    Disjoint (Set.range (finalZeroExteriorComponent hπ data D s hs hstart hk))
      (Set.range (finalTerminalComponent hπ data D s hs hk hp i)) := by
  rw [ProjectiveLine.map_range_left_infinity
    (finalTerminalComponent hπ data D s hs hk hp i), finalTerminalComponent_infinity]
  exact Set.disjoint_union_right.mpr
    ⟨(finalZeroExteriorComponent_later_chart_disjoint hπ data D s hs hstart hk s hs0
      (by omega)).mono_right
      (finalTerminalComponent_left_range_chart hπ data D s hs hk hp (by omega) i),
    finalZeroExteriorComponent_terminal_node_disjoint hπ data D s hs hk hp hstart⟩

end FLT.Mazur.WeierstrassDividedDepth
