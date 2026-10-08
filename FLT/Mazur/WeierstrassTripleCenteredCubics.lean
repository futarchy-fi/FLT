/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleCenteredRelations
public import FLT.Mazur.WeierstrassTripleTangentSlopeAlgebra

/-!
# Centered divided differences for all four ordinary triple laws

Retain the two individual inner product relations and center both outer cubic
relations. These are polynomial consequences of the original chart equations.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- The first inner divided difference, centered at its second input. -/
theorem triple_first_product {x₁ x₂ y₁ y₂ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hc : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) :
    (x₁ - x₂) * (W.addX x₁ x₂ l - x₂) =
      (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) -
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) * l := by
  simp only [Affine.addX]
  linear_combination (l + W.a₁) * hl + hc

/-- The second inner divided difference, centered at its first input. -/
theorem triple_last_product {x₂ x₃ y₂ y₃ m : R}
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hc : m * (y₂ + y₃ + W.a₁ * x₃ + W.a₃) =
      x₂ ^ 2 + x₂ * x₃ + x₃ ^ 2 + W.a₂ * (x₂ + x₃) + W.a₄ - W.a₁ * y₂) :
    (x₃ - x₂) * (W.addX x₂ x₃ m - x₂) =
      (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) -
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) * m := by
  simp only [Affine.addX]
  linear_combination -m * hm + hc

/-- The left outer divided difference has the centered tangent form. -/
theorem triple_left_cubic_centered {x₁ x₂ x₃ y₁ y₂ y₃ l m n : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hc : n * (W.addY x₁ x₂ y₁ l + y₃ + W.a₁ * x₃ + W.a₃) =
      (W.addX x₁ x₂ l) ^ 2 + W.addX x₁ x₂ l * x₃ + x₃ ^ 2 +
        W.a₂ * (W.addX x₁ x₂ l + x₃) + W.a₄ - W.a₁ * W.addY x₁ x₂ y₁ l) :
    let u := W.addX x₁ x₂ l - x₂
    let z := x₃ - x₂
    n * (-(l + W.a₁) * u + (m + W.a₁) * z) =
      u ^ 2 + u * z + z ^ 2 + (W.a₂ + 3 * x₂) * (u + z) +
        (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) +
        W.a₁ * (l + W.a₁) * u + W.a₁ * (W.a₃ + W.a₁ * x₂ + 2 * y₂) := by
  dsimp only
  simp only [Affine.addY, Affine.negY, Affine.negAddY] at hc
  linear_combination hc - (n + W.a₁) * hl - n * hm

/-- The right outer divided difference has the centered tangent form. -/
theorem triple_right_cubic_centered {x₁ x₂ x₃ y₁ y₂ l m o : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hc : o * (y₁ + W.addY x₂ x₃ y₂ m + W.a₁ * W.addX x₂ x₃ m + W.a₃) =
      x₁ ^ 2 + x₁ * W.addX x₂ x₃ m + (W.addX x₂ x₃ m) ^ 2 +
        W.a₂ * (x₁ + W.addX x₂ x₃ m) + W.a₄ - W.a₁ * y₁) :
    let x := x₁ - x₂
    let v := W.addX x₂ x₃ m - x₂
    o * (l * x - m * v) =
      x ^ 2 + x * v + v ^ 2 + (W.a₂ + 3 * x₂) * (x + v) +
        (W.a₄ + 2 * W.a₂ * x₂ + 3 * x₂ ^ 2 - W.a₁ * y₂) - W.a₁ * l * x := by
  dsimp only
  simp only [Affine.addY, Affine.negY, Affine.negAddY] at hc
  linear_combination hc + (o + W.a₁) * hl

end FLT.Mazur.WeierstrassIntegralAddition
