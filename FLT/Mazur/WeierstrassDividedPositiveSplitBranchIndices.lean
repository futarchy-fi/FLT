/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityBranchIndices
public import FLT.Mazur.WeierstrassDividedFinalBranchChains

/-!
# Original positive-start branches with their common strict terminal node

Each branch contains its original initial node, every retained node, and the
common terminal node. Only the last vertex is shared between the two branches.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The full positive-start branch, including the common terminal vertex. -/
def positiveSplitBranchNode (start s : ℕ) (hstart : 0 < start)
    (j : Fin (s + 3)) (i : Fin 2) : FinalNodeIndex start s :=
  if h : j.val < s + 2 then
    .inl (positiveEqualityBranchNode start s hstart ⟨j.val, h⟩ i)
  else .inr ()

/-- Before the terminal vertex, the original initial and retained nodes are unchanged. -/
theorem positiveSplitBranchNode_attachment (start s : ℕ) (hstart : 0 < start)
    (j : Fin (s + 2)) (i : Fin 2) :
    positiveSplitBranchNode start s hstart ⟨j.val, by omega⟩ i =
      .inl (positiveEqualityBranchNode start s hstart j i) := by
  simp only [positiveSplitBranchNode, dite_eq_left j.isLt]

/-- The first vertex is the original initial node in the specified tangent order. -/
theorem positiveSplitBranchNode_initial (start s : ℕ) (hstart : 0 < start) (i : Fin 2) :
    positiveSplitBranchNode start s hstart 0 i = .inl (.inl ⟨i, hstart⟩) := by
  simp only [positiveSplitBranchNode, Fin.val_zero,
    dite_eq_left (show 0 < s + 2 by omega)]
  rfl

/-- The original retained branch follows immediately after the initial node. -/
theorem positiveSplitBranchNode_tail (start s : ℕ) (hstart : 0 < start)
    (j : Fin (s + 2)) (i : Fin 2) :
    positiveSplitBranchNode start s hstart ⟨j.val + 1, by omega⟩ i =
      finalBranchVertex start s j i := by
  by_cases hj : j.val < s + 1
  · rw [positiveSplitBranchNode, dite_eq_left (show j.val + 1 < s + 2 by omega),
      positiveEqualityBranchNode_retained start s hstart ⟨j.val, hj⟩,
      finalBranchVertex, dite_eq_left hj]
  · rw [positiveSplitBranchNode, dite_eq_right (show ¬j.val + 1 < s + 2 by omega),
      finalBranchVertex, dite_eq_right hj]

/-- Both complete branches terminate at the same original strict terminal node. -/
theorem positiveSplitBranchNode_terminal (start s : ℕ) (hstart : 0 < start) (i : Fin 2) :
    positiveSplitBranchNode start s hstart ⟨s + 2, by omega⟩ i = .inr () := by
  simp only [positiveSplitBranchNode, lt_self_iff_false, dite_false]

end FLT.Mazur.WeierstrassDividedDepth
