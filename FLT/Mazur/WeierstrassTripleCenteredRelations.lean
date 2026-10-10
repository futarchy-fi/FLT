/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleSlopeAlgebra

/-!
# Centering ordinary triple-addition relations at the middle input

The actual Weierstrass line and divided-difference equations imply the scalar
cross relation and outer-line identities used in the triple slope calculation.
No coordinate difference is canceled in this translation.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- The two inner divided differences give the centered cross relation. -/
theorem triple_inner_cross {x₁ x₂ x₃ y₁ y₂ y₃ l m : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hcl : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
    (hcm : m * (y₂ + y₃ + W.a₁ * x₃ + W.a₃) =
      x₂ ^ 2 + x₂ * x₃ + x₃ ^ 2 + W.a₂ * (x₂ + x₃) + W.a₄ - W.a₁ * y₂) :
    (x₁ - x₂) * (W.addX x₁ x₂ l - x₂) -
        (x₃ - x₂) * (W.addX x₂ x₃ m - x₂) =
      (W.a₃ + W.a₁ * x₂ + 2 * y₂) * (m - l) := by
  simp only [Affine.addX]
  linear_combination (l + W.a₁) * hl + hcl + m * hm - hcm

/-- The left outer line equation in centered coordinates. -/
theorem triple_left_line_centered {x₁ x₂ x₃ y₁ y₂ y₃ l m n : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hn : n * (W.addX x₁ x₂ l - x₃) = W.addY x₁ x₂ y₁ l - y₃) :
    n * ((W.addX x₁ x₂ l - x₂) - (x₃ - x₂)) =
      -(l + W.a₁) * (W.addX x₁ x₂ l - x₂) -
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) - m * (x₃ - x₂) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY] at hn
  linear_combination hn + hl - hm

/-- The right outer line equation in centered coordinates. -/
theorem triple_right_line_centered {x₁ x₂ x₃ y₁ y₂ l m o : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (ho : o * (x₁ - W.addX x₂ x₃ m) = y₁ - W.addY x₂ x₃ y₂ m) :
    o * ((x₁ - x₂) - (W.addX x₂ x₃ m - x₂)) =
      l * (x₁ - x₂) + (m + W.a₁) * (W.addX x₂ x₃ m - x₂) +
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY] at ho
  linear_combination ho - hl

/-- Centering the left ordinate uses only the first inner line equation. -/
theorem triple_left_ordinate_centered {x₁ x₂ x₃ y₁ y₂ l n : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂) :
    W.addY (W.addX x₁ x₂ l) x₃ (W.addY x₁ x₂ y₁ l) n - y₂ =
      -(n + W.a₁) * (W.addX (W.addX x₁ x₂ l) x₃ n - x₂) +
        (n + l + W.a₁) * (W.addX x₁ x₂ l - x₂) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  linear_combination -hl

/-- Centering the right ordinate retains the translated constant term. -/
theorem triple_right_ordinate_centered {x₁ x₂ x₃ y₁ y₂ l m o : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂) :
    W.addY x₁ (W.addX x₂ x₃ m) y₁ o - y₂ =
      -(o + W.a₁) * (W.addX x₁ (W.addX x₂ x₃ m) o - x₂) +
        (o - l) * (x₁ - x₂) - (W.a₃ + W.a₁ * x₂ + 2 * y₂) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  linear_combination hl

end FLT.Mazur.WeierstrassIntegralAddition
