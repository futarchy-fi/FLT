/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalSecantResidue

/-!
# Unequal secants with a middle-depth terminal input

At the exact middle depth the terminal constant coefficient is nonzero.
Its equation forces both terminal branch factors to be nonzero, so either
branch of the shallower input has a smooth difference-depth output. The
terminal abscissa may vanish.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c6 x y u v i l : K)
local notation "X" => unequalSecantX W 0 0 0 0 c6 x y u v i
local notation "Y" => unequalSecantY W 0 0 0 0 c6 x y u v i l

/-- A middle-depth terminal equation forces both terminal branch factors to be nonzero. -/
theorem unequalSecant_middle_factors (hc : v ^ 2 + W.a₁ * u * v = c6) (h6 : c6 ≠ 0) :
    v ≠ 0 ∧ v + W.a₁ * u ≠ 0 := by
  have hf : v * (v + W.a₁ * u) = c6 := by linear_combination hc
  exact mul_ne_zero_iff.mp (hf.symm ▸ h6)

/-- On the positive shallow branch, the terminal ordinate controls the output abscissa. -/
theorem unequalSecant_middle_positive (h2 : W.a₂ = 0)
    (hi : i * x = 1) (hl : l * x = y) (hy : y = 0) :
    X = -(W.a₁ * x * v * i ^ 2) ∧ Y = -W.a₁ * X := by
  have hx := (unequalSecant_residue_inverse x i hi).2
  have hsl : l = 0 := (mul_eq_zero.mp (hl.trans hy)).resolve_right hx
  constructor
  · simp only [unequalSecantX, unequalSecantNumerator, h2, hy]
    ring
  · simp only [unequalSecantY, hsl, zero_add, zero_mul, add_zero]

/-- On the other shallow branch, the opposite terminal branch factor controls the output. -/
theorem unequalSecant_middle_negative (h2 : W.a₂ = 0)
    (hi : i * x = 1) (hl : l * x = y) (hy : y = -W.a₁ * x) :
    X = W.a₁ * x * (v + W.a₁ * u) * i ^ 2 ∧ Y = 0 := by
  have hx := (unequalSecant_residue_inverse x i hi).2
  have hsl : l = -W.a₁ := (mul_left_inj' hx).mp (hl.trans hy)
  constructor
  · simp only [unequalSecantX, unequalSecantNumerator, h2, hy]
    ring
  · simp only [unequalSecantY, hsl, neg_add_cancel, neg_zero, zero_mul, add_zero]

/-- Both shallow branches give smooth outputs without puncturing the middle-depth input. -/
theorem unequalSecant_middle_vertical (h2 : W.a₂ = 0) (ha : W.a₁ ≠ 0)
    (hi : i * x = 1) (hl : l * x = y)
    (hc : v ^ 2 + W.a₁ * u * v = c6) (h6 : c6 ≠ 0)
    (hb : y = 0 ∨ y = -W.a₁ * x) : 2 * Y + W.a₁ * X ≠ 0 := by
  have hix := unequalSecant_residue_inverse x i hi
  obtain ⟨hv, hw⟩ := unequalSecant_middle_factors W c6 u v hc h6
  rcases hb with hy | hy
  · obtain ⟨hX, hY⟩ := unequalSecant_middle_positive W c6 x y u v i l h2 hi hl hy
    have h : 2 * Y + W.a₁ * X = -(W.a₁ * X) := by rw [hY]; ring
    rw [h, neg_ne_zero, hX]
    exact mul_ne_zero ha (neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hix.2) hv) (pow_ne_zero 2 hix.1)))
  · obtain ⟨hX, hY⟩ := unequalSecant_middle_negative W c6 x y u v i l h2 hi hl hy
    rw [hY, mul_zero, zero_add, hX]
    exact mul_ne_zero ha (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hix.2) hw)
      (pow_ne_zero 2 hix.1))

end FLT.Mazur.WeierstrassDilatation
