/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalCentering
public import FLT.Mazur.WeierstrassTripleCenteredCubics

/-!
# Centering the reversed outer cubic equations

The actual reciprocal tangent denominators and equations translate to the centered
cubic expressions. These identities hold over arbitrary commutative rings.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Center the left outer reversed tangent denominator. -/
theorem reciprocal_left_cubic_denominator_centered {x₁ x₂ x₃ y₁ y₂ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂) :
    (W.toAffine.addX x₁ x₂ l) ^ 2 + W.toAffine.addX x₁ x₂ l * x₃ + x₃ ^ 2 +
        W.a₂ * (W.toAffine.addX x₁ x₂ l + x₃) + W.a₄ -
        W.a₁ * W.toAffine.addY x₁ x₂ y₁ l =
      let u := W.toAffine.addX x₁ x₂ l - x₂
      let z := x₃ - x₂
      u ^ 2 + u * z + z ^ 2 + (W.a₂ + 3 * x₂) * (u + z) +
        (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) +
        W.a₁ * (l + W.a₁) * u + W.a₁ * (W.a₃ + W.a₁ * x₂ + 2 * y₂) := by
  dsimp only
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  linear_combination -W.a₁ * hl

/-- Center the right outer reversed tangent denominator. -/
theorem reciprocal_right_cubic_denominator_centered {x₁ x₂ x₃ y₁ y₂ l m : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂) :
    x₁ ^ 2 + x₁ * W.toAffine.addX x₂ x₃ m + (W.toAffine.addX x₂ x₃ m) ^ 2 +
        W.a₂ * (x₁ + W.toAffine.addX x₂ x₃ m) + W.a₄ - W.a₁ * y₁ =
      let x := x₁ - x₂
      let v := W.toAffine.addX x₂ x₃ m - x₂
      x ^ 2 + x * v + v ^ 2 + (W.a₂ + 3 * x₂) * (x + v) +
        (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) - W.a₁ * l * x := by
  dsimp only
  linear_combination W.a₁ * hl

/-- Center the reciprocal left outer divided difference. -/
theorem reciprocal_left_cubic_centered {x₁ x₂ x₃ y₁ y₂ y₃ l m r : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hc : r * ((W.toAffine.addX x₁ x₂ l) ^ 2 +
        W.toAffine.addX x₁ x₂ l * x₃ + x₃ ^ 2 +
        W.a₂ * (W.toAffine.addX x₁ x₂ l + x₃) + W.a₄ -
        W.a₁ * W.toAffine.addY x₁ x₂ y₁ l) =
      W.toAffine.addY x₁ x₂ y₁ l + y₃ + W.a₁ * x₃ + W.a₃) :
    let u := W.toAffine.addX x₁ x₂ l - x₂
    let z := x₃ - x₂
    r * (u ^ 2 + u * z + z ^ 2 + (W.a₂ + 3 * x₂) * (u + z) +
        (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) +
        W.a₁ * (l + W.a₁) * u + W.a₁ * (W.a₃ + W.a₁ * x₂ + 2 * y₂)) =
      -(l + W.a₁) * u + (m + W.a₁) * z := by
  rw [reciprocal_left_cubic_denominator_centered W hl] at hc
  dsimp only at hc ⊢
  simp only [Affine.addY, Affine.negY, Affine.negAddY] at hc
  linear_combination hc + hl + hm

/-- Center the reciprocal right outer divided difference. -/
theorem reciprocal_right_cubic_centered {x₁ x₂ x₃ y₁ y₂ l m s : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hc : s * (x₁ ^ 2 + x₁ * W.toAffine.addX x₂ x₃ m +
        (W.toAffine.addX x₂ x₃ m) ^ 2 +
        W.a₂ * (x₁ + W.toAffine.addX x₂ x₃ m) + W.a₄ - W.a₁ * y₁) =
      y₁ + W.toAffine.addY x₂ x₃ y₂ m +
        W.a₁ * W.toAffine.addX x₂ x₃ m + W.a₃) :
    let x := x₁ - x₂
    let v := W.toAffine.addX x₂ x₃ m - x₂
    s * (x ^ 2 + x * v + v ^ 2 + (W.a₂ + 3 * x₂) * (x + v) +
        (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) - W.a₁ * l * x) =
      l * x - m * v := by
  rw [reciprocal_right_cubic_denominator_centered W hl] at hc
  dsimp only at hc ⊢
  simp only [Affine.addY, Affine.negY, Affine.negAddY] at hc
  linear_combination hc - hl

end FLT.Mazur.WeierstrassIntegralAddition
