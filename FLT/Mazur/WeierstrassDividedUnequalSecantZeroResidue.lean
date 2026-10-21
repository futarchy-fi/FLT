/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalSecantResidue

/-!
# Zero-depth secants preserve the puncture of a nodal terminal input

The shallow scale is one, so its cubic term must be retained. The actual
unequal-depth formula cannot send a punctured terminal point to the node.
Combined with the terminal nodal equation this forces a nonzero vertical
output derivative in every characteristic, with no branch choice.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (x y u v i l : K)
local notation "N" => unequalSecantNumerator W 1 0 0 0 0 x y u v
local notation "X" => unequalSecantX W 1 0 0 0 0 x y u v i
local notation "Y" => unequalSecantY W 1 0 0 0 0 x y u v i l

/-- A punctured zero-depth secant cannot collapse a nonzero terminal abscissa to the node. -/
theorem unequalSecant_zero_noncollapse (h2 : W.a₂ = 0) (hi : i * x = 1)
    (he : y ^ 2 + W.a₁ * x * y = x ^ 3) (hu : u ≠ 0) : X ≠ 0 ∨ Y ≠ 0 := by
  have hix := unequalSecant_residue_inverse x i hi
  by_cases hX : X = 0
  · right
    intro hY
    have hN : N = 0 := by
      exact (mul_eq_zero.mp hX).resolve_right (pow_ne_zero 2 hix.1)
    have hc : y * u - x * v = 0 := by
      have h : (y * u - x * v) * i = 0 := by
        simpa only [unequalSecantY, hX, mul_zero, neg_zero, zero_add, sub_zero,
          one_mul] using hY
      exact (mul_eq_zero.mp h).resolve_right hix.1
    have hxu : x ^ 3 * u = 0 := by
      simp only [unequalSecantNumerator, h2] at hN
      linear_combination -x * hN - 2 * u * he + (2 * y + W.a₁ * x) * hc
    exact (mul_ne_zero (pow_ne_zero 3 hix.2) hu) hxu
  · exact Or.inl hX

/-- The constructed nodal output has a nonzero vertical derivative without a branch premise. -/
theorem unequalSecant_zero_vertical (h2 : W.a₂ = 0) (ha : W.a₁ ≠ 0)
    (hi : i * x = 1) (he : y ^ 2 + W.a₁ * x * y = x ^ 3) (hu : u ≠ 0)
    (hout : Y ^ 2 + W.a₁ * X * Y = 0) : 2 * Y + W.a₁ * X ≠ 0 := by
  intro hv
  have hf : Y * (Y + W.a₁ * X) = 0 := by linear_combination hout
  have hY : Y = 0 := by
    rcases mul_eq_zero.mp hf with h | h
    · exact h
    · linear_combination hv - h
  have hX : X = 0 := by
    apply (mul_eq_zero.mp (show W.a₁ * X = 0 by linear_combination hv - 2 * hY))
      |>.resolve_left ha
  exact (unequalSecant_zero_noncollapse W x y u v i l h2 hi he hu).elim
    (fun h => h hX) (fun h => h hY)

end FLT.Mazur.WeierstrassDilatation
