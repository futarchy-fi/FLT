/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchResidue

/-!
# Reflected residues at an even terminal input

At zero terminal residual depth the square term survives. The terminal
input equation identifies its difference from the constant, so the
reflected output is still punctured and vertically smooth.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c6 x u r i : K)
  (hxu : IsUnit (x * u))
local notation "X" => reflectedBranchX 1 0 c6 x u 0 r i hxu
local notation "Y" => reflectedBranchY W 0 1 0 c6 0 x u 0 r i 0 hxu

/-- The reflected intercept is the full terminal ordinate. -/
theorem reflectedTerminal_intercept (hi : i * x = 1) :
    sumDepthIntercept 1 x u 0 r i = r := by
  unfold sumDepthIntercept
  linear_combination r * hi

/-- The surviving square is determined by the original terminal input equation. -/
theorem reflectedTerminalX_relation (hi : i * x = 1)
    (he : r ^ 2 + W.a₁ * u * r = c6) : X * x = -W.a₁ * r := by
  have hu : u ≠ 0 := (mul_ne_zero_iff.mp hxu.ne_zero).2
  apply mul_right_cancel₀ hu
  have hX : X * (x * u) = r ^ 2 - c6 := by
    unfold reflectedBranchX
    rw [reflectedTerminal_intercept x u r i hi, mul_assoc, hxu.val_inv_mul]
    ring
  linear_combination hX + he

/-- Exact terminal constant depth prevents the terminal ordinate from vanishing. -/
theorem reflectedTerminal_ordinate_ne_zero (hc6 : c6 ≠ 0)
    (he : r ^ 2 + W.a₁ * u * r = c6) : r ≠ 0 := by
  intro h
  apply hc6
  simpa only [h, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using he.symm

/-- The terminal reflected output is punctured without discarding its square term. -/
theorem reflectedTerminalX_ne_zero (ha : W.a₁ ≠ 0) (hc6 : c6 ≠ 0)
    (hi : i * x = 1) (he : r ^ 2 + W.a₁ * u * r = c6) : X ≠ 0 := by
  have hn := mul_ne_zero (neg_ne_zero.mpr ha)
    (reflectedTerminal_ordinate_ne_zero W c6 u r hc6 he)
  intro h
  apply hn
  have hr := reflectedTerminalX_relation W c6 x u r i hxu hi he
  simpa only [h, zero_mul] using hr.symm

/-- The actual leading reflected ordinate lies on the negative branch. -/
theorem reflectedTerminalY_relation : Y = -W.a₁ * X := by
  simp only [reflectedBranchY, zero_add, zero_mul, sub_zero]

/-- Even terminal reflected residues have nonzero vertical derivative in every characteristic. -/
theorem reflectedTerminal_vertical (ha : W.a₁ ≠ 0) (hc6 : c6 ≠ 0)
    (hi : i * x = 1) (he : r ^ 2 + W.a₁ * u * r = c6) :
    2 * Y + W.a₁ * X ≠ 0 := by
  rw [reflectedTerminalY_relation]
  have h : 2 * (-W.a₁ * X) + W.a₁ * X = -W.a₁ * X := by ring
  rw [h]
  exact mul_ne_zero (neg_ne_zero.mpr ha)
    (reflectedTerminalX_ne_zero W c6 x u r i hxu ha hc6 hi he)

end FLT.Mazur.WeierstrassDilatation
