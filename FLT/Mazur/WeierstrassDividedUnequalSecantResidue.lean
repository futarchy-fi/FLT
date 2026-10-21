/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalSecantFormula

/-!
# Difference-depth outputs at opposite residue branches

At opposite punctured branches the divided unequal-depth secant output
has nonzero vertical derivative. This remains true when the deeper input
has contracted to the node at the shallower depth.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (x y u v i l : K)
local notation "X" => unequalSecantX W 0 0 0 0 0 x y u v i
local notation "Y" => unequalSecantY W 0 0 0 0 0 x y u v i l

/-- The inverse and abscissa remain nonzero after specialization. -/
theorem unequalSecant_residue_inverse (hi : i * x = 1) : i ≠ 0 ∧ x ≠ 0 := by
  exact ⟨fun h => zero_ne_one (by simpa only [h, zero_mul] using hi),
    fun h => zero_ne_one (by simpa only [h, mul_zero] using hi)⟩

/-- From the positive branch to the negative branch the output is on the negative branch. -/
theorem unequalSecant_residue_positive_negative (h2 : W.a₂ = 0)
    (hi : i * x = 1) (hl : l * x = y) (hy : y = 0) (hv : v = -W.a₁ * u) :
    X = W.a₁ ^ 2 * x * u * i ^ 2 ∧ Y = -W.a₁ * X := by
  have hx := (unequalSecant_residue_inverse x i hi).2
  have hsl : l = 0 := (mul_eq_zero.mp (hl.trans hy)).resolve_right hx
  constructor
  · simp only [unequalSecantX, unequalSecantNumerator, h2, hy, hv]
    ring
  · simp only [unequalSecantY, hsl, zero_add, zero_mul, add_zero]

/-- The opposite orientation produces a positive-branch output at the same depth. -/
theorem unequalSecant_residue_negative_positive (h2 : W.a₂ = 0)
    (hi : i * x = 1) (hl : l * x = y) (hy : y = -W.a₁ * x) (hv : v = 0) :
    X = W.a₁ ^ 2 * x * u * i ^ 2 ∧ Y = 0 := by
  have hx := (unequalSecant_residue_inverse x i hi).2
  have hsl : l = -W.a₁ := (mul_left_inj' hx).mp (hl.trans hy)
  constructor
  · simp only [unequalSecantX, unequalSecantNumerator, h2, hy, hv]
    ring
  · simp only [unequalSecantY, hsl, neg_add_cancel, neg_zero, zero_mul, add_zero]

/-- Both opposite-branch orientations have nonzero output vertical derivative. -/
theorem unequalSecant_residue_vertical (h2 : W.a₂ = 0) (ha : W.a₁ ≠ 0)
    (hi : i * x = 1) (hl : l * x = y) (hu : u ≠ 0)
    (hbranch : (y = 0 ∧ v = -W.a₁ * u) ∨ (y = -W.a₁ * x ∧ v = 0)) :
    2 * Y + W.a₁ * X ≠ 0 := by
  have hix := unequalSecant_residue_inverse x i hi
  have hn : W.a₁ ^ 2 * x * u * i ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hix.2) hu)
      (pow_ne_zero 2 hix.1)
  rcases hbranch with ⟨hy, hv⟩ | ⟨hy, hv⟩
  · obtain ⟨hX, hY⟩ := unequalSecant_residue_positive_negative W x y u v i l h2 hi hl hy hv
    have h : 2 * Y + W.a₁ * X = -(W.a₁ * X) := by rw [hY]; ring
    rw [h, neg_ne_zero, hX]
    exact mul_ne_zero ha hn
  · obtain ⟨hX, hY⟩ := unequalSecant_residue_negative_positive W x y u v i l h2 hi hl hy hv
    rw [hY, mul_zero, zero_add, hX]
    exact mul_ne_zero ha hn

end FLT.Mazur.WeierstrassDilatation
