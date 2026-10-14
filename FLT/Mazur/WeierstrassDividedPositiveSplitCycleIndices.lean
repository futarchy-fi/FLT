/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitBranchIndices

/-!
# Cyclic ordering of all original positive-start strict nodes

The two initial nodes, all retained pairs, and the common terminal node occur
exactly once in a cycle of length `2 * s + 5`.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- First full branch, common terminal node, then the opposite full branch in reverse. -/
def positiveSplitCycleNodeIndex (start s : ℕ) (hstart : 0 < start)
    (i : Fin (2 * s + 5)) : FinalNodeIndex start s :=
  if h : i.val < s + 2 then
    .inl (positiveEqualityBranchNode start s hstart ⟨i.val, h⟩ 0)
  else if ht : i.val = s + 2 then .inr ()
  else .inl (positiveEqualityBranchNode start s hstart ⟨2 * s + 4 - i.val, by omega⟩ 1)

/-- First-branch attachment positions increase from the original initial node. -/
theorem positiveSplitCycleNodeIndex_first (start s : ℕ) (hstart : 0 < start)
    (j : Fin (s + 2)) :
    positiveSplitCycleNodeIndex start s hstart ⟨j.val, by omega⟩ =
      positiveSplitBranchNode start s hstart ⟨j.val, by omega⟩ 0 := by
  rw [positiveSplitCycleNodeIndex, dite_eq_left j.isLt, positiveSplitBranchNode_attachment]

/-- The original terminal node separates the two full branches. -/
theorem positiveSplitCycleNodeIndex_terminal (start s : ℕ) (hstart : 0 < start) :
    positiveSplitCycleNodeIndex start s hstart ⟨s + 2, by omega⟩ = .inr () := by
  simp only [positiveSplitCycleNodeIndex, lt_self_iff_false, dite_false, dite_true]

/-- Second-branch attachment positions decrease towards the opposite original initial node. -/
theorem positiveSplitCycleNodeIndex_second (start s : ℕ) (hstart : 0 < start)
    (j : Fin (s + 2)) :
    positiveSplitCycleNodeIndex start s hstart ⟨2 * s + 4 - j.val, by omega⟩ =
      positiveSplitBranchNode start s hstart ⟨j.val, by omega⟩ 1 := by
  rw [positiveSplitCycleNodeIndex, dite_eq_right (show ¬2 * s + 4 - j.val < s + 2 by omega),
    dite_eq_right (show ¬2 * s + 4 - j.val = s + 2 by omega),
    positiveSplitBranchNode_attachment]
  congr 2
  apply Fin.ext
  change 2 * s + 4 - (2 * s + 4 - j.val) = j.val
  omega

/-- Every cyclic position names a distinct original node. -/
theorem positiveSplitCycleNodeIndex_injective (start s : ℕ) (hstart : 0 < start) :
    Function.Injective (positiveSplitCycleNodeIndex start s hstart) := by
  intro i j hij
  unfold positiveSplitCycleNodeIndex at hij
  split_ifs at hij <;> try cases hij
  all_goals try
    have H := positiveEqualityBranchNode_injective start s hstart
      (a₁ := (_, _)) (a₂ := (_, _)) (Sum.inl.inj hij)
    simp only [Prod.mk.injEq, Fin.mk.injEq, and_true, zero_ne_one,
      and_false, one_ne_zero] at H
  all_goals (apply Fin.ext; omega)

/-- The cycle exhausts both original initial nodes, all retained pairs, and the terminal node. -/
theorem positiveSplitCycleNodeIndex_surjective (start s : ℕ) (hstart : 0 < start) :
    Function.Surjective (positiveSplitCycleNodeIndex start s hstart) := by
  rintro (a | ⟨⟩)
  · obtain ⟨⟨j, i⟩, rfl⟩ := positiveEqualityBranchNode_surjective start s hstart a
    fin_cases i
    · refine ⟨⟨j.val, by omega⟩, ?_⟩
      rw [positiveSplitCycleNodeIndex_first, positiveSplitBranchNode_attachment]
      rfl
    · refine ⟨⟨2 * s + 4 - j.val, by omega⟩, ?_⟩
      rw [positiveSplitCycleNodeIndex_second, positiveSplitBranchNode_attachment]
      rfl
  · exact ⟨⟨s + 2, by omega⟩, positiveSplitCycleNodeIndex_terminal start s hstart⟩

/-- The full original node family is exactly the cyclic index type. -/
def positiveSplitCycleNodeEquiv (start s : ℕ) (hstart : 0 < start) :
    Fin (2 * s + 5) ≃ FinalNodeIndex start s :=
  Equiv.ofBijective (positiveSplitCycleNodeIndex start s hstart)
    ⟨positiveSplitCycleNodeIndex_injective start s hstart,
      positiveSplitCycleNodeIndex_surjective start s hstart⟩

end FLT.Mazur.WeierstrassDividedDepth
