/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantFormula

/-!
# The second divided slope open, including equal abscissae

Invert the divided ordinate sum rather than the divided abscissa difference.
The divided equations determine the line relation even when the two abscissae
coincide. No cancellation or inversion of the original scale is needed.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 b4 b6 : R) {u₁ u₂ v₁ v₂ l : R}

/-- On the second divided slope open, the chord relation determines the line relation. -/
theorem divided_tangent_relation
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6)
    (hu : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
    (hc : l * (v₁ + v₂ + W.a₁ * u₂ + b3) =
      s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁) :
    l * (u₁ - u₂) = v₁ - v₂ := by
  apply hu.mul_left_inj.mp
  linear_combination (u₁ - u₂) * hc -
    divided_equation_difference W s b3 b4 b6 h₁ h₂

/-- The actual original cubic equation holds on the second divided slope open. -/
theorem divided_tangent_add_equation
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6)
    (hu : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
    (hc : l * (v₁ + v₂ + W.a₁ * u₂ + b3) =
      s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁) :
    W.toAffine.Equation (W.toAffine.addX (s * u₁) (s * u₂) l)
      (W.toAffine.addY (s * u₁) (s * u₂) (s * v₁) l) := by
  apply WeierstrassIntegralAddition.equation_add_of_relations (y₂ := s * v₂)
  · rw [Affine.equation_iff]
    simp only [h3, h4, h6]
    linear_combination s ^ 2 * h₁
  · linear_combination s * divided_tangent_relation W s b3 b4 b6 h₁ h₂ hu hc
  · simp only [h3, h4]
    linear_combination s * hc

end FLT.Mazur.WeierstrassDilatation
