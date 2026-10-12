/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CyclicPinchingReflection

/-!
# Arithmetic of reflected component and node positions

Compute the original cyclic reflection in natural-number coordinates. These
formulas distinguish the fixed terminal component from its exchanged attachments.
-/

@[expose] public section
namespace FLT.Mazur.PolygonPinching
variable {n : ℕ} [NeZero n]

/-- Component reflection is negation in the original finite cyclic ring. -/
theorem reflectIndex_eq_neg (i : Fin n) : reflectIndex i = -i := by
  simp only [reflectIndex, ← map_neg, RingEquiv.symm_apply_apply]

/-- Node reflection has the additional minus-one offset. -/
theorem reflectNodeIndex_eq_neg_sub_one (i : Fin n) : reflectNodeIndex i = -i - 1 := by
  simp only [reflectNodeIndex, map_sub, map_neg, map_one, RingEquiv.symm_apply_apply]

/-- Away from component zero, reflection subtracts the position from the cycle length. -/
theorem reflectIndex_val (i : Fin n) (hi : i ≠ 0) : (reflectIndex i).val = n - i.val := by
  rw [reflectIndex_eq_neg, Fin.val_neg, ite_eq_right hi]

/-- The node offset makes the natural-number formula uniform, even at node zero. -/
theorem reflectNodeIndex_val (i : Fin n) : (reflectNodeIndex i).val = n - 1 - i.val := by
  rw [reflectNodeIndex_eq_neg_sub_one]
  by_cases hi : i = 0
  · subst i
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    simp only [neg_zero, zero_sub, Fin.coe_neg_one, Fin.val_zero, Nat.sub_zero,
      Nat.add_one_sub_one]
  · rw [Fin.val_sub_one_of_ne_zero (neg_ne_zero.mpr hi), Fin.val_neg, ite_eq_right hi]
    omega

variable (s : ℕ)

/-- The first chain position goes to the same level of the second chain. -/
theorem reflectIndex_firstChain (j : Fin (s + 1)) :
    reflectIndex (⟨j.val + 1, by omega⟩ : Fin (2 * s + 4)) =
      ⟨2 * s + 3 - j.val, by omega⟩ := by
  apply Fin.ext
  rw [reflectIndex_val _ (by intro h; have := congrArg Fin.val h; simp at this)]
  dsimp only
  omega

/-- The second chain position returns to the same level of the first chain. -/
theorem reflectIndex_secondChain (j : Fin (s + 1)) :
    reflectIndex (⟨2 * s + 3 - j.val, by omega⟩ : Fin (2 * s + 4)) =
      ⟨j.val + 1, by omega⟩ := by
  rw [← reflectIndex_firstChain s j, reflectIndex_reflectIndex]

/-- The single terminal component is fixed by reflection. -/
theorem reflectIndex_terminal :
    reflectIndex (⟨s + 2, by omega⟩ : Fin (2 * s + 4)) = ⟨s + 2, by omega⟩ := by
  apply Fin.ext
  rw [reflectIndex_val _ (by intro h; have := congrArg Fin.val h; simp at this)]
  dsimp only
  omega

/-- First-branch nodes, including both ends, go to second-branch nodes at the same level. -/
theorem reflectNodeIndex_firstChain (j : Fin (s + 2)) :
    reflectNodeIndex (⟨j.val, by omega⟩ : Fin (2 * s + 4)) =
      ⟨2 * s + 3 - j.val, by omega⟩ := by
  apply Fin.ext
  rw [reflectNodeIndex_val]
  dsimp only
  omega

/-- Second-branch nodes return to first-branch nodes without a level shift. -/
theorem reflectNodeIndex_secondChain (j : Fin (s + 2)) :
    reflectNodeIndex (⟨2 * s + 3 - j.val, by omega⟩ : Fin (2 * s + 4)) =
      ⟨j.val, by omega⟩ := by
  rw [← reflectNodeIndex_firstChain s j, reflectNodeIndex_reflectNodeIndex]

end FLT.Mazur.PolygonPinching
