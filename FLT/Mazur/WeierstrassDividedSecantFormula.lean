/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralAdditionFormula

/-!
# Secants between two divided inputs

The difference of the divided abscissae is the denominator, even when the
common scale vanishes. The divided equations prove the original addition
relations without cancelling that scale or assuming either input is smooth.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 b4 b6 : R) {u₁ u₂ v₁ v₂ l : R}

/-- Divided equations have a divided difference with no factor of the scale. -/
theorem divided_equation_difference
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6) :
    (v₁ + v₂ + W.a₁ * u₂ + b3) * (v₁ - v₂) =
      (u₁ - u₂) *
        (s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁) := by
  linear_combination h₁ - h₂

/-- Only the divided abscissa difference must be invertible. -/
theorem divided_secant_relation
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6)
    (hu : IsUnit (u₁ - u₂)) (hl : l * (u₁ - u₂) = v₁ - v₂) :
    l * (v₁ + v₂ + W.a₁ * u₂ + b3) =
      s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁ := by
  apply hu.mul_left_inj.mp
  linear_combination divided_equation_difference W s b3 b4 b6 h₁ h₂ +
    (v₁ + v₂ + W.a₁ * u₂ + b3) * hl

/-- A divided secant gives an actual point of the unchanged original equation. -/
theorem divided_secant_add_equation
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6)
    (hu : IsUnit (u₁ - u₂)) (hl : l * (u₁ - u₂) = v₁ - v₂) :
    W.toAffine.Equation (W.toAffine.addX (s * u₁) (s * u₂) l)
      (W.toAffine.addY (s * u₁) (s * u₂) (s * v₁) l) := by
  apply WeierstrassIntegralAddition.equation_add_of_relations (y₂ := s * v₂)
  · rw [Affine.equation_iff]
    simp only [h3, h4, h6]
    linear_combination s ^ 2 * h₁
  · linear_combination s * hl
  · have hc := divided_secant_relation W s b3 b4 b6 h₁ h₂ hu hl
    simp only [h3, h4]
    linear_combination s * hc

end FLT.Mazur.WeierstrassDilatation
