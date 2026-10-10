/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityNodeFamily

/-!
# Cyclic ordering of the actual equality-depth attachments

The first ordered branch runs inward and the second runs outward. The
terminal projective line joins them directly, without any extra node.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The two retained branches in cyclic order, with no terminal-node position. -/
def zeroEqualityCycleNodeIndex (start s : ℕ) (i : Fin (2 * s + 2)) :
    EqualityNodeIndex start s :=
  if h : i.val < s + 1 then .inr (⟨i.val, h⟩, 0)
  else .inr (⟨2 * s + 1 - i.val, by omega⟩, 1)

/-- The first branch occupies its original increasing positions. -/
theorem zeroEqualityCycleNodeIndex_first (start s : ℕ) (j : Fin (s + 1)) :
    zeroEqualityCycleNodeIndex start s ⟨j.val, by omega⟩ = .inr (j, 0) := by
  simp only [zeroEqualityCycleNodeIndex, dite_eq_left j.isLt]

/-- The opposite branch occupies the remaining positions in decreasing order. -/
theorem zeroEqualityCycleNodeIndex_second (start s : ℕ) (j : Fin (s + 1)) :
    zeroEqualityCycleNodeIndex start s ⟨2 * s + 1 - j.val, by omega⟩ = .inr (j, 1) := by
  have h : ¬2 * s + 1 - j.val < s + 1 := by omega
  simp only [zeroEqualityCycleNodeIndex, dite_eq_right h]
  congr 2
  apply Fin.ext
  change 2 * s + 1 - (2 * s + 1 - j.val) = j.val
  omega

/-- Every cyclic position names a different original ordered attachment. -/
theorem zeroEqualityCycleNodeIndex_injective (start s : ℕ) :
    Function.Injective (zeroEqualityCycleNodeIndex start s) := by
  intro i j hij
  unfold zeroEqualityCycleNodeIndex at hij
  split_ifs at hij <;>
    simp_all only [Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq,
      and_true, zero_ne_one, and_false, one_ne_zero] <;>
    apply Fin.ext <;> omega

/-- At start zero the cyclic list contains all original attachment indices. -/
theorem zeroEqualityCycleNodeIndex_surjective (start s : ℕ) (hstart : start = 0) :
    Function.Surjective (zeroEqualityCycleNodeIndex start s) := by
  rintro (⟨i, hi⟩ | ⟨j, i⟩)
  · omega
  · fin_cases i
    · exact ⟨⟨j.val, by omega⟩, zeroEqualityCycleNodeIndex_first start s j⟩
    · exact ⟨⟨2 * s + 1 - j.val, by omega⟩, zeroEqualityCycleNodeIndex_second start s j⟩

/-- The complete start-zero cyclic ordering of equality-depth attachment indices. -/
def zeroEqualityCycleNodeEquiv (start s : ℕ) (hstart : start = 0) :
    Fin (2 * s + 2) ≃ EqualityNodeIndex start s :=
  Equiv.ofBijective (zeroEqualityCycleNodeIndex start s)
    ⟨zeroEqualityCycleNodeIndex_injective start s,
      zeroEqualityCycleNodeIndex_surjective start s hstart⟩

end FLT.Mazur.WeierstrassDividedDepth
