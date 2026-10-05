/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Integral slope relations for Weierstrass addition

The two nonvertical slope charts work over arbitrary commutative rings,
including rings with zero divisors. Their equations imply that the usual
addition coordinates satisfy the cubic, without passage to a fraction field.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- The divided difference identity for two solutions of the cubic. -/
theorem equation_difference {x₁ x₂ y₁ y₂ : R}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) :
    (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * (y₁ - y₂) =
      (x₁ - x₂) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) := by
  rw [Affine.equation_iff] at h₁ h₂
  linear_combination h₁ - h₂

/-- Two polynomial slope relations suffice for addition to preserve the cubic. -/
theorem equation_add_of_relations {x₁ x₂ y₁ y₂ l : R}
    (h₁ : W.Equation x₁ y₁) (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hc : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) :
    W.Equation (W.addX x₁ x₂ l) (W.addY x₁ x₂ y₁ l) := by
  apply (Affine.equation_neg ..).mpr
  rw [Affine.equation_iff] at h₁ ⊢
  simp only [Affine.addX, Affine.negAddY]
  linear_combination h₁ +
    (l ^ 2 + W.a₁ * l - W.a₂ - 2 * x₁ - x₂) * (hc - l * hl)

/-- On the secant open, the line relation implies the second slope relation. -/
theorem secant_relation {x₁ x₂ y₁ y₂ l : R}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hu : IsUnit (x₁ - x₂)) (hl : l * (x₁ - x₂) = y₁ - y₂) :
    l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ := by
  apply hu.mul_left_inj.mp
  linear_combination equation_difference W h₁ h₂ +
    (y₁ + y₂ + W.a₁ * x₂ + W.a₃) * hl

/-- On the second slope open, the divided difference determines the line relation. -/
theorem tangent_relation {x₁ x₂ y₁ y₂ l : R}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hu : IsUnit (y₁ + y₂ + W.a₁ * x₂ + W.a₃))
    (hc : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) :
    l * (x₁ - x₂) = y₁ - y₂ := by
  apply hu.mul_left_inj.mp
  linear_combination (x₁ - x₂) * hc - equation_difference W h₁ h₂

end FLT.Mazur.WeierstrassIntegralAddition
