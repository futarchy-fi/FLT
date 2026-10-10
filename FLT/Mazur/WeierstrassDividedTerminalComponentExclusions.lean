/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentPairIntersections
public import FLT.Mazur.WeierstrassDividedFinalTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalAllExteriorNodes
public import FLT.Mazur.WeierstrassDividedTerminalLineDisjoint

/-!
# Complete terminal components exclude earlier nodes and distant lines

Both full affine pieces and the original terminal node are retained in these exclusions.
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
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R

/-- The terminal node misses each entire original retained chart. -/
theorem terminalNode_retainedTensorChart_disjoint (a : ℕ) (ha : a ≤ s) :
    Disjoint (Set.range (finalNodeSection hπ data D s hs hk hp (.inr ())))
      (Set.range (retainedTensorChartAt hπ data (s + 1) hs a (by omega))) := by
  rw [retainedTensorChartAt_range_index]
  have he : (⟨s + 1 - a + 1, by omega⟩ : Fin (s + 1 + 3)) =
      (⟨s - a, by omega⟩ : Fin (s + 2)).succ.succ := Fin.ext (by dsimp; omega)
  rw [he]
  exact terminalNode_globalExteriorIndex_disjoint hπ data D s hs hk hp _

/-- The full left affine chart of a positive terminal component lies in the last retained chart. -/
theorem finalTerminalComponent_left_range_chart (hpos : 0 < start + s) (i : Fin 2) :
    Set.range (ProjectiveLine.left K ≫ finalTerminalComponent hπ data D s hs hk hp i) ⊆
      Set.range (retainedTensorChartAt hπ data (s + 1) hs s (by omega)) := by
  rw [retainedTensorChartAt_original hπ data s hs 0 hs,
    olderGlobalTensorChart_zero_retention,
    finalTerminalComponent_positive hπ data D s hs hk hp hpos]
  fin_cases i
  · change Set.range (ProjectiveLine.left K ≫
      terminalFirstComponent hπ data D s hs hpos hk hp) ⊆ _
    rw [terminalFirstComponent_left]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · change Set.range (ProjectiveLine.left K ≫
      terminalSecondComponent hπ data D s hs hpos hk hp) ⊆ _
    rw [terminalSecondComponent_left]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩

/-- The right affine chart of either terminal component lies in the original terminal node chart. -/
theorem finalTerminalComponent_right_range_chart (hpos : 0 < start + s) (i : Fin 2) :
    Set.range (ProjectiveLine.right K ≫ finalTerminalComponent hπ data D s hs hk hp i) ⊆
      Set.range (terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp) := by
  rw [finalTerminalComponent_positive hπ data D s hs hk hp hpos]
  fin_cases i
  · change Set.range (ProjectiveLine.right K ≫
      terminalFirstComponent hπ data D s hs hpos hk hp) ⊆ _
    rw [terminalFirstComponent_right]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · change Set.range (ProjectiveLine.right K ≫
      terminalSecondComponent hπ data D s hs hpos hk hp) ⊆ _
    rw [terminalSecondComponent_right]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩

/-- Every earlier retained node misses either complete terminal component. -/
theorem retainedNode_terminalComponent_disjoint (a : ℕ) (ha : a < s) (i k : Fin 2) :
    Disjoint (Set.range (retainedNodeSectionAt hπ data D (s + 1) hs a
        (by omega) (by omega) i))
      (Set.range (finalTerminalComponent hπ data D s hs hk hp k)) := by
  rw [ProjectiveLine.map_range_left_infinity, finalTerminalComponent_infinity]
  apply Set.disjoint_union_right.mpr
  constructor
  · exact (retainedNodeSectionAt_later_disjoint hπ data D (s + 1) hs a s ha
      (by omega) (by omega) i).mono_right
      (finalTerminalComponent_left_range_chart hπ data D s hs hk hp (by omega) k)
  · exact ((terminalNode_retainedTensorChart_disjoint hπ data D s hs hk hp a
      (by omega)).mono_right
      (retainedNodeSectionAt_range hπ data D (s + 1) hs a (by omega) (by omega) i)).symm

/-- A line at an earlier retained level misses the complete terminal component. -/
theorem retainedLine_terminalComponent_disjoint (a : ℕ) (ha : a < s)
    (hpos : 0 < start + a) (i k : Fin 2) :
    Disjoint (Set.range (retainedLineAt hπ data D (s + 1) hs a
        (by omega) hpos (by omega) i))
      (Set.range (finalTerminalComponent hπ data D s hs hk hp k)) := by
  rw [ProjectiveLine.map_range_left_infinity, finalTerminalComponent_infinity]
  apply Set.disjoint_union_right.mpr
  constructor
  · exact (retainedLineAt_later_disjoint hπ data D (s + 1) hs a s ha
      (by omega) hpos (by omega) i).mono_right
      (finalTerminalComponent_left_range_chart hπ data D s hs hk hp (by omega) k)
  · exact ((terminalNode_retainedTensorChart_disjoint hπ data D s hs hk hp a
      (by omega)).mono_right
      (retainedLineAt_range hπ data D (s + 1) hs a (by omega) hpos (by omega) i)).symm

/-- Nonadjacent full retained and terminal components are disjoint in either branch. -/
theorem finalAdjacent_terminal_nonadjacent_disjoint (a : Fin s)
    (ha : a.val + 2 ≤ s) (i k : Fin 2) :
    Disjoint (Set.range (finalAdjacentComponent hπ data D s hs hk a i))
      (Set.range (finalTerminalComponent hπ data D s hs hk hp k)) := by
  rw [finalAdjacentComponent_range_line_node]
  exact Set.disjoint_union_left.mpr
    ⟨retainedLine_terminalComponent_disjoint hπ data D s hs hk hp
      (a.val + 1) (by omega) (by omega) i k,
    retainedNode_terminalComponent_disjoint hπ data D s hs hk hp a.val a.isLt i k⟩

end FLT.Mazur.WeierstrassDividedDepth
