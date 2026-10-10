/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalComponentExclusions

/-!
# The last retained component meets its terminal successor at the original node

Matching tangent orders give exactly their common marked section. Crossed orders
have empty intersection, including when the first retained component has scale one.
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

/-- The entire last retained horizontal line misses the original terminal node chart. -/
theorem retainedLastLine_terminalChart_disjoint (hpos : 0 < start + s) (i : Fin 2) :
    Disjoint (Set.range (retainedLineAt hπ data D (s + 1) hs s (by omega) hpos hk i))
      (Set.range (terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp)) := by
  rw [retainedLineAt_original hπ data D s hs 0 hs]
  fin_cases i
  · change Disjoint (Set.range (olderGlobalMiddleFirstLine hπ data D s hs 0 hs hpos hk)) _
    unfold olderGlobalMiddleFirstLine
    rw [olderGlobalTensorChart_zero_retention]
    exact (terminalNodeLine_disjoint hπ data D s hs hpos hk _ _ hp).symm
  · change Disjoint (Set.range (olderGlobalMiddleSecondLine hπ data D s hs 0 hs hpos hk)) _
    unfold olderGlobalMiddleSecondLine
    rw [olderGlobalTensorChart_zero_retention]
    exact (terminalNodeLine_disjoint hπ data D s hs hpos hk _ _ hp).symm

/-- Only the last retained line and the terminal component's original zero node can meet. -/
theorem finalAdjacent_terminal_range_inter_reduce (a : Fin s) (ha : a.val + 1 = s)
    (i k : Fin 2) :
    Set.range (finalAdjacentComponent hπ data D s hs hk a i) ∩
        Set.range (finalTerminalComponent hπ data D s hs hk hp k) =
      Set.range (retainedLineAt hπ data D (s + 1) hs s (by omega) (by omega) hk i) ∩
      Set.range (retainedNodeSectionAt hπ data D (s + 1) hs s (by omega) hk k) := by
  have Hn := retainedNode_terminalComponent_disjoint hπ data D s hs hk hp a.val a.isLt i k
  rw [ProjectiveLine.map_range_right_zero, finalTerminalComponent_zero] at Hn
  rw [finalAdjacentComponent_range_line_node,
    retainedLineAt_level_congr hπ data D (s + 1) hs
      (b := s) _ (by omega) _ (by omega) _ hk ha i,
    ProjectiveLine.map_range_right_zero, finalTerminalComponent_zero]
  rw [Set.union_comm (Set.range (retainedLineAt _ _ _ _ _ _ _ _ _ _))]
  apply componentRange_union_inter
  · exact (Set.disjoint_union_right.mp Hn).1
  · exact (Set.disjoint_union_right.mp Hn).2
  · exact (retainedLastLine_terminalChart_disjoint hπ data D s hs hk hp (by omega) i).mono_right
      (finalTerminalComponent_right_range_chart hπ data D s hs hk hp (by omega) k)

/-- Matching last retained and terminal components meet exactly in their original retained node. -/
theorem finalAdjacent_terminal_successive_range_inter (a : Fin s) (ha : a.val + 1 = s)
    (i : Fin 2) :
    Set.range (finalAdjacentComponent hπ data D s hs hk a i) ∩
        Set.range (finalTerminalComponent hπ data D s hs hk hp i) =
      Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (⟨s, by omega⟩, i)))) := by
  rw [finalAdjacent_terminal_range_inter_reduce hπ data D s hs hk hp a ha]
  exact Set.inter_eq_right.mpr
    (retainedNodeSectionAt_range_line hπ data D (s + 1) hs s (by omega) (by omega) hk i)

/-- Opposite tangent orders have no intersection at the last retained/terminal transition. -/
theorem finalAdjacent_terminal_successive_cross_disjoint (a : Fin s) (ha : a.val + 1 = s)
    (i k : Fin 2) (hik : i ≠ k) :
    Disjoint (Set.range (finalAdjacentComponent hπ data D s hs hk a i))
      (Set.range (finalTerminalComponent hπ data D s hs hk hp k)) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [finalAdjacent_terminal_range_inter_reduce hπ data D s hs hk hp a ha]
  exact Set.disjoint_iff_inter_eq_empty.mp
    (retainedLineAt_cross_node_disjoint hπ data D (s + 1) hs s (by omega) (by omega) hk i k hik)

end FLT.Mazur.WeierstrassDividedDepth
