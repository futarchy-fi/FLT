/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineCoordinates

/-!
# Recovering normalized coordinates from a negated line and one minor

A line through the negation of a normalized point gives explicit reconstruction
formulas for any other normalized point. No leading coefficient or coordinate
is inverted. This keeps the comparison valid over nonreduced coefficient rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The X difference is controlled by one homogeneous minor and the line residual. -/
theorem infinity_negated_line_difference_x {u v m b : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) (x z : R) :
    x - u = -(1 + W.a₃ * b) *
        ((-1 - W.a₁ * u - W.a₃ * v) * x - u * (-1 - W.a₁ * x - W.a₃ * z)) +
      W.a₃ * u * (z - m * x - b * (-1 - W.a₁ * x - W.a₃ * z)) := by
  linear_combination -W.a₃ * x * h

/-- The Z difference has a division-free reconstruction from the same two residuals. -/
theorem infinity_negated_line_difference_z {u v m b : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) (x z : R) :
    z - v = (W.a₁ * b - m) *
        ((-1 - W.a₁ * u - W.a₃ * v) * x - u * (-1 - W.a₁ * x - W.a₃ * z)) +
      (1 + W.a₃ * v) * (z - m * x - b * (-1 - W.a₁ * x - W.a₃ * z)) := by
  linear_combination -(1 + W.a₃ * z) * h

/-- The negated Y difference is also reconstructed without assuming that Y is a unit. -/
theorem infinity_negated_line_difference_y {u v m b : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) (x z : R) :
    (-1 - W.a₁ * x - W.a₃ * z) - (-1 - W.a₁ * u - W.a₃ * v) =
      (W.a₁ + W.a₃ * m) *
        ((-1 - W.a₁ * u - W.a₃ * v) * x - u * (-1 - W.a₁ * x - W.a₃ * z)) +
      W.a₃ * (-1 - W.a₁ * u - W.a₃ * v) *
        (z - m * x - b * (-1 - W.a₁ * x - W.a₃ * z)) := by
  linear_combination -W.a₃ * (-1 - W.a₁ * x - W.a₃ * z) * h

/-- A candidate equals the reference point exactly when its line residual and minor vanish. -/
theorem infinity_negated_line_eq_iff {u v m b x z : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) :
    (x = u ∧ z = v) ↔
      z - m * x - b * (-1 - W.a₁ * x - W.a₃ * z) = 0 ∧
        (-1 - W.a₁ * u - W.a₃ * v) * x - u * (-1 - W.a₁ * x - W.a₃ * z) = 0 := by
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨h, by ring⟩
  · rintro ⟨hl, hm⟩
    have hx := infinity_negated_line_difference_x W h x z
    have hz := infinity_negated_line_difference_z W h x z
    rw [hl, hm] at hx hz
    constructor
    · linear_combination hx
    · linear_combination hz

end FLT.Mazur.WeierstrassIntegralChart
