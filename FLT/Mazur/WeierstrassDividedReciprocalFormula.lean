/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantFormula
public import FLT.Mazur.WeierstrassReciprocalAdditionFormula

/-!
# Reciprocal slopes for two arbitrary divided inputs

Invert the divided ordinate difference. This includes opposite-branch pairs
with equal abscissae, without inverting the original scale. Their reciprocal
slope is zero and the homogeneous output is the original point at infinity.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve WeierstrassIntegralAddition
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 b4 b6 : R) {u₁ u₂ v₁ v₂ m : R}

/-- The divided ordinate difference cancels without any hypothesis on the scale. -/
theorem divided_reciprocal_relation
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6)
    (hu : IsUnit (v₁ - v₂)) (hm : m * (v₁ - v₂) = u₁ - u₂) :
    m * (s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁) =
      v₁ + v₂ + W.a₁ * u₂ + b3 := by
  apply hu.mul_left_inj.mp
  linear_combination
    (s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁) * hm -
      divided_equation_difference W s b3 b4 b6 h₁ h₂

/-- The homogeneous reciprocal output satisfies the unchanged original cubic. -/
theorem divided_reciprocal_add_equation
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6)
    (hu : IsUnit (v₁ - v₂)) (hm : m * (v₁ - v₂) = u₁ - u₂) :
    W.toProjective.Equation (reciprocalXYZ W (s * u₁) (s * u₂) (s * v₁) m) := by
  apply equation_reciprocalXYZ (y₂ := s * v₂)
  · rw [Affine.equation_iff]
    simp only [h3, h4, h6]
    linear_combination s ^ 2 * h₁
  · linear_combination s * hm
  · have hc := divided_reciprocal_relation W s b3 b4 b6 h₁ h₂ hu hm
    simp only [h3, h4]
    linear_combination s * hc

/-- Equal abscissae on this open have zero reciprocal slope and unit output ordinate. -/
theorem divided_reciprocal_equal_abscissa
    (hu : IsUnit (v₁ - v₂)) (hm : m * (v₁ - v₂) = u₁ - u₂) (hx : u₁ = u₂) :
    m = 0 ∧ reciprocalXYZ W (s * u₁) (s * u₂) (s * v₁) m = ![0, -1, 0] := by
  have hz : m = 0 := hu.mul_left_inj.mp (by simpa only [hx, sub_self, zero_mul] using hm)
  refine ⟨hz, ?_⟩
  rw [hz, reciprocalXYZ_zero]

end FLT.Mazur.WeierstrassDilatation
