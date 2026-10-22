/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthFormula

/-!
# Cancellation of the quadratic quotient in sum-depth residues

Both branch ordinates retain the finite quadratic coefficient quotient.
Their contributions cancel in the intercept, giving the same nonzero
sum abscissa and zero ordinate in every residue characteristic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (β x u q r i : K)
  (hxu : IsUnit (x * u))
local notation "b" => sumDepthIntercept 1 x u q r i
local notation "X" => sumDepthX 1 0 0 x u q r i hxu
local notation "Y" => sumDepthY W 1 0 0 x u q r i 0 hxu

/-- The divided intercept has its nonzero leading coefficient on the positive branch. -/
theorem factoredSumDepthIntercept_residue (hi : i * x = 1)
    (hq : W.a₁ * q = x ^ 2 + β * x) (hr : W.a₁ * r = β * u) :
    W.a₁ * b = -(x * u) := by
  calc
    W.a₁ * b = (x * (W.a₁ * r) - (W.a₁ * q) * u) * i := by
      unfold sumDepthIntercept
      ring
    _ = -(x * u) := by rw [hq, hr]; linear_combination -x * u * hi

/-- The leading abscissa is the product of the input abscissae divided by a1 squared. -/
theorem factoredSumDepthX_residue (hi : i * x = 1)
    (hq : W.a₁ * q = x ^ 2 + β * x) (hr : W.a₁ * r = β * u) :
    W.a₁ ^ 2 * X = x * u := by
  have hb := factoredSumDepthIntercept_residue W β x u q r i hi hq hr
  have hX : X * (x * u) = b ^ 2 := by
    unfold sumDepthX
    rw [mul_assoc, hxu.val_inv_mul]
    ring
  apply hxu.mul_left_inj.mp
  calc
    (W.a₁ ^ 2 * X) * (x * u) = W.a₁ ^ 2 * (X * (x * u)) := by ring
    _ = (W.a₁ * b) ^ 2 := by rw [hX]; ring
    _ = (x * u) * (x * u) := by rw [hb]; ring

/-- The sum of two positive branches has zero divided ordinate on the closed fiber. -/
theorem factoredSumDepthY_residue (ha : W.a₁ ≠ 0)
    (hi : i * x = 1)
    (hq : W.a₁ * q = x ^ 2 + β * x) (hr : W.a₁ * r = β * u) : Y = 0 := by
  have hb := factoredSumDepthIntercept_residue W β x u q r i hi hq hr
  have hX := factoredSumDepthX_residue W β x u q r i hxu hi hq hr
  apply (mul_left_inj' ha).mp
  simp only [sumDepthY, zero_add, sub_zero]
  linear_combination -hX - hb

/-- The constructed sum-depth output is vertically smooth at every such punctured input pair. -/
theorem factoredSumDepth_residue_vertical (ha : W.a₁ ≠ 0)
    (hi : i * x = 1)
    (hq : W.a₁ * q = x ^ 2 + β * x) (hr : W.a₁ * r = β * u) : 2 * Y + W.a₁ * X ≠ 0 := by
  have hX := factoredSumDepthX_residue W β x u q r i hxu hi hq hr
  have hx : X ≠ 0 := by
    intro h
    apply hxu.ne_zero
    rw [h, mul_zero] at hX
    exact hX.symm
  rw [factoredSumDepthY_residue W β x u q r i hxu ha hi hq hr, mul_zero, zero_add]
  exact mul_ne_zero ha hx

end FLT.Mazur.WeierstrassDividedDepth
