/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalAdditionFormula
public import FLT.Mazur.WeierstrassTripleCenteredRelations

/-!
# Centering reciprocal homogeneous coordinates

These polynomial identities translate genuine chart coordinates to the centered
variables used in the triple-output calculation. No localization is needed.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The left reciprocal secant denominator in centered coordinates. -/
theorem reciprocal_left_denominator_centered {x₁ x₂ x₃ y₁ y₂ y₃ l m : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃) :
    W.toAffine.addY x₁ x₂ y₁ l - y₃ =
      -(l + W.a₁) * (W.toAffine.addX x₁ x₂ l - x₂) -
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) - m * (x₃ - x₂) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  linear_combination hl - hm

/-- The right reciprocal secant denominator in centered coordinates. -/
theorem reciprocal_right_denominator_centered {x₁ x₂ x₃ y₁ y₂ l m : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂) :
    y₁ - W.toAffine.addY x₂ x₃ y₂ m =
      l * (x₁ - x₂) + (m + W.a₁) * (W.toAffine.addX x₂ x₃ m - x₂) +
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  linear_combination -hl

/-- Centering the x-coordinate of any reciprocal output is polynomial. -/
theorem reciprocalXYZ_centered_x (x₀ x₁ x₂ y₁ r : R) :
    reciprocalXYZ W x₁ x₂ y₁ r 0 - x₀ * r ^ 3 =
      r * (1 + W.a₁ * r - (W.a₂ + x₁ + x₂ + x₀) * r ^ 2) := by
  simp only [reciprocalXYZ, reciprocalH, Matrix.cons_val_zero]
  ring

/-- Centering the y-coordinate retains the translated constant term. -/
theorem reciprocalXYZ_centered_y (x₀ y₀ x₁ x₂ y₁ r : R) :
    reciprocalXYZ W x₁ x₂ y₁ r 1 - y₀ * r ^ 3 =
      -(1 + W.a₁ * r) * (1 + W.a₁ * r - (W.a₂ + x₁ + x₂ + x₀) * r ^ 2) +
        (x₁ - x₀) * r ^ 2 - (y₁ + y₀ + W.a₃ + W.a₁ * x₀) * r ^ 3 := by
  simp only [reciprocalXYZ, reciprocalH, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- The left intermediate ordinate has the required centered constant. -/
theorem reciprocal_left_ordinate_constant {x₁ x₂ y₁ y₂ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂) :
    W.toAffine.addY x₁ x₂ y₁ l + y₂ + W.a₃ + W.a₁ * x₂ =
      -(l + W.a₁) * (W.toAffine.addX x₁ x₂ l - x₂) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  linear_combination hl

end FLT.Mazur.WeierstrassIntegralAddition
