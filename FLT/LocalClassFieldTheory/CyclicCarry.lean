/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RationalTorsion

/-!
# The positive cyclic carry cocycle

The section i ↦ i.val/n of Z/n → Q/Z has integral coboundary equal to the
carry in addition modulo n. This is the sign convention used for the local
fundamental class in Milne, Class Field Theory, III, pp. 101–102.
No identification with a local Galois group is asserted here.
-/

@[expose] public section

namespace LocalClassFieldTheory

variable {n : ℕ} [NeZero n]

/-- The integer carry for addition modulo n. -/
def cyclicCarry (i j : ZMod n) : ℤ := if n ≤ i.val + j.val then 1 else 0

/-- Multiplying the carry by n gives the discrepancy of integer representatives. -/
theorem cyclicCarry_mul (i j : ZMod n) :
    cyclicCarry i j * n = (i.val : ℤ) + j.val - (i + j).val := by
  unfold cyclicCarry
  split_ifs with h
  · have hv := ZMod.val_add_val_of_le h
    omega
  · have hv := ZMod.val_add_of_lt (Nat.lt_of_not_ge h)
    omega

/-- The carry is the positive coboundary of the rational representative section. -/
theorem cyclicCarry_rat (i j : ZMod n) :
    (cyclicCarry i j : ℚ) = (j.val : ℚ) / n - ((i + j).val : ℚ) / n +
      (i.val : ℚ) / n := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h : (cyclicCarry i j : ℚ) * n = (i.val : ℚ) + j.val - (i + j).val := by
    exact_mod_cast cyclicCarry_mul i j
  field_simp
  linarith

/-- The chosen rational representative lifts the positive Q/Z character. -/
theorem cyclicCarry_section (i : ZMod n) :
    (↑((i.val : ℚ) / n) : AddCircle (1 : ℚ)) = zmodToRatCircle n i :=
  (zmodToRatCircle_apply n i).symm

/-- The integral carry satisfies the two-cocycle equation for the trivial action. -/
theorem cyclicCarry_cocycle (i j k : ZMod n) :
    cyclicCarry (i + j) k + cyclicCarry i j =
      cyclicCarry j k + cyclicCarry i (j + k) := by
  apply mul_right_cancel₀ (show (n : ℤ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne n))
  simp only [add_mul, cyclicCarry_mul, add_assoc]
  abel

/-- The carry is normalized in its first argument. -/
@[simp] theorem cyclicCarry_zero_left (j : ZMod n) : cyclicCarry 0 j = 0 := by
  simp [cyclicCarry, Nat.not_le.mpr (ZMod.val_lt j)]

/-- The carry is normalized in its second argument. -/
@[simp] theorem cyclicCarry_zero_right (i : ZMod n) : cyclicCarry i 0 = 0 := by
  simp [cyclicCarry, Nat.not_le.mpr (ZMod.val_lt i)]

/-- Exponentiating the carry gives the multiplicative two-cocycle used for a uniformizer. -/
theorem cyclicCarry_zpow_cocycle {A : Type*} [CommGroup A] (a : A) (i j k : ZMod n) :
    a ^ cyclicCarry (i + j) k * a ^ cyclicCarry i j =
      a ^ cyclicCarry j k * a ^ cyclicCarry i (j + k) := by
  simp only [← zpow_add, cyclicCarry_cocycle]

end LocalClassFieldTheory
