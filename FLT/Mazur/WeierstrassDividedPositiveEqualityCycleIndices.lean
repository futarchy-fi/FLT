/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityBranchIndices

/-!
# Cyclic ordering of the actual equality-depth attachments

The first branch runs inward from its initial node and the second runs outward.
The two initial attachments occur as well as every retained attachment.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Both complete branches in cyclic order, including the initial node on each. -/
def positiveEqualityCycleNodeIndex (start s : ℕ) (hstart : 0 < start) (i : Fin (2 * s + 4)) :
    EqualityNodeIndex start s :=
  if h : i.val < s + 2 then positiveEqualityBranchNode start s hstart ⟨i.val, h⟩ 0
  else positiveEqualityBranchNode start s hstart ⟨2 * s + 3 - i.val, by omega⟩ 1

/-- The first branch occupies its original increasing positions. -/
theorem positiveEqualityCycleNodeIndex_first (start s : ℕ) (hstart : 0 < start) (j : Fin (s + 2)) :
    positiveEqualityCycleNodeIndex start s hstart ⟨j.val, by omega⟩ =
      positiveEqualityBranchNode start s hstart j 0 := by
  simp only [positiveEqualityCycleNodeIndex, dite_eq_left j.isLt]

/-- The opposite branch occupies the remaining positions in decreasing order. -/
theorem positiveEqualityCycleNodeIndex_second (start s : ℕ) (hstart : 0 < start) (j : Fin (s + 2)) :
    positiveEqualityCycleNodeIndex start s hstart ⟨2 * s + 3 - j.val, by omega⟩ =
      positiveEqualityBranchNode start s hstart j 1 := by
  have h : ¬2 * s + 3 - j.val < s + 2 := by omega
  simp only [positiveEqualityCycleNodeIndex, dite_eq_right h]
  congr 1
  apply Fin.ext
  change 2 * s + 3 - (2 * s + 3 - j.val) = j.val
  omega

/-- Every cyclic position names a different original ordered attachment. -/
theorem positiveEqualityCycleNodeIndex_injective (start s : ℕ) (hstart : 0 < start) :
    Function.Injective (positiveEqualityCycleNodeIndex start s hstart) := by
  intro i j hij
  unfold positiveEqualityCycleNodeIndex at hij
  split_ifs at hij <;>
    have H := positiveEqualityBranchNode_injective start s hstart
      (a₁ := (_, _)) (a₂ := (_, _)) hij <;>
    simp only [Prod.mk.injEq, Fin.mk.injEq, and_true, zero_ne_one,
      and_false, one_ne_zero] at H <;>
    apply Fin.ext <;> omega

/-- Every initial and retained attachment occurs in the cyclic order. -/
theorem positiveEqualityCycleNodeIndex_surjective (start s : ℕ) (hstart : 0 < start) :
    Function.Surjective (positiveEqualityCycleNodeIndex start s hstart) := by
  intro x
  obtain ⟨⟨j, i⟩, rfl⟩ := positiveEqualityBranchNode_surjective start s hstart x
  fin_cases i
  · exact ⟨⟨j.val, by omega⟩, positiveEqualityCycleNodeIndex_first start s hstart j⟩
  · exact ⟨⟨2 * s + 3 - j.val, by omega⟩,
      positiveEqualityCycleNodeIndex_second start s hstart j⟩

/-- The positive-start cyclic ordering retains every original attachment exactly once. -/
def positiveEqualityCycleNodeEquiv (start s : ℕ) (hstart : 0 < start) :
    Fin (2 * s + 4) ≃ EqualityNodeIndex start s :=
  Equiv.ofBijective (positiveEqualityCycleNodeIndex start s hstart)
    ⟨positiveEqualityCycleNodeIndex_injective start s hstart,
      positiveEqualityCycleNodeIndex_surjective start s hstart⟩

end FLT.Mazur.WeierstrassDividedDepth
