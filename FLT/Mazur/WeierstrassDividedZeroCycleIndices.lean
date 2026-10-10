/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeFamily

/-!
# Cyclic ordering of the original start-zero split-terminal nodes

The first retained branch runs inward, followed by the common terminal node,
then the second retained branch runs outward. Every original node occurs once.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Explicit cyclic order: first branch, terminal node, second branch in reverse order. -/
def zeroSplitCycleNodeIndex (start s : ℕ) (i : Fin (2 * s + 3)) : FinalNodeIndex start s :=
  if h : i.val < s + 1 then .inl (.inr (⟨i.val, h⟩, 0))
  else if ht : i.val = s + 1 then .inr ()
  else .inl (.inr (⟨2 * s + 2 - i.val, by omega⟩, 1))

/-- The first branch occupies exactly the first s+1 positions. -/
theorem zeroSplitCycleNodeIndex_first (start s : ℕ) (j : Fin (s + 1)) :
    zeroSplitCycleNodeIndex start s ⟨j.val, by omega⟩ = .inl (.inr (j, 0)) := by
  simp only [zeroSplitCycleNodeIndex, dite_eq_left j.isLt]

/-- The original terminal node sits between the two branches. -/
theorem zeroSplitCycleNodeIndex_terminal (start s : ℕ) :
    zeroSplitCycleNodeIndex start s ⟨s + 1, by omega⟩ = .inr () := by
  simp only [zeroSplitCycleNodeIndex, lt_self_iff_false, dite_false, dite_true]

/-- The second branch occupies precisely the remaining positions, in decreasing order. -/
theorem zeroSplitCycleNodeIndex_second (start s : ℕ) (j : Fin (s + 1)) :
    zeroSplitCycleNodeIndex start s ⟨2 * s + 2 - j.val, by omega⟩ =
      .inl (.inr (j, 1)) := by
  have h₁ : ¬2 * s + 2 - j.val < s + 1 := by omega
  have h₂ : ¬2 * s + 2 - j.val = s + 1 := by omega
  simp only [zeroSplitCycleNodeIndex, dite_eq_right h₁, dite_eq_right h₂]
  congr 3
  apply Fin.ext
  change 2 * s + 2 - (2 * s + 2 - j.val) = j.val
  omega

/-- Distinct cyclic positions never name the same original node. -/
theorem zeroSplitCycleNodeIndex_injective (start s : ℕ) :
    Function.Injective (zeroSplitCycleNodeIndex start s) := by
  intro i j hij
  unfold zeroSplitCycleNodeIndex at hij
  split_ifs at hij <;>
    simp_all only [Fin.isValue, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq,
      and_true, zero_ne_one, and_false, lt_self_iff_false, not_false_eq_true, one_ne_zero] <;>
    apply Fin.ext <;> omega

/-- At start zero there are no additional initial nodes outside this cyclic list. -/
theorem zeroSplitCycleNodeIndex_surjective (start s : ℕ) (hstart : start = 0) :
    Function.Surjective (zeroSplitCycleNodeIndex start s) := by
  rintro ((⟨i, hi⟩ | ⟨j, i⟩) | ⟨⟩)
  · omega
  · fin_cases i
    · exact ⟨⟨j.val, by omega⟩, zeroSplitCycleNodeIndex_first start s j⟩
    · exact ⟨⟨2 * s + 2 - j.val, by omega⟩, zeroSplitCycleNodeIndex_second start s j⟩
  · exact ⟨⟨s + 1, by omega⟩, zeroSplitCycleNodeIndex_terminal start s⟩

/-- The explicit cycle is an equivalence with the complete original node family. -/
def zeroSplitCycleNodeEquiv (start s : ℕ) (hstart : start = 0) :
    Fin (2 * s + 3) ≃ FinalNodeIndex start s :=
  Equiv.ofBijective (zeroSplitCycleNodeIndex start s)
    ⟨zeroSplitCycleNodeIndex_injective start s,
      zeroSplitCycleNodeIndex_surjective start s hstart⟩

end FLT.Mazur.WeierstrassDividedDepth
