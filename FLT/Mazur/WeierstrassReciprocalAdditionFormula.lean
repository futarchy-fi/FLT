/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralAdditionFormula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# Integral reciprocal-slope addition formulas

Using the reciprocal slope gives homogeneous coordinates regular at vertical
chords and tangents. At reciprocal slope zero the result is infinity.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The numerator of the affine x-coordinate in reciprocal-slope coordinates. -/
def reciprocalH (x₁ x₂ m : R) : R :=
  1 + W.a₁ * m - (W.a₂ + x₁ + x₂) * m ^ 2

/-- Homogeneous addition coordinates, defined even at reciprocal slope zero. -/
def reciprocalXYZ (x₁ x₂ y₁ m : R) : Fin 3 → R :=
  ![m * reciprocalH W x₁ x₂ m,
    -(1 + W.a₁ * m) * reciprocalH W x₁ x₂ m + x₁ * m ^ 2 - (y₁ + W.a₃) * m ^ 3,
    m ^ 3]

/-- Reciprocal slope zero gives the point at infinity with a unit y-coordinate. -/
@[simp] theorem reciprocalXYZ_zero (x₁ x₂ y₁ : R) :
    reciprocalXYZ W x₁ x₂ y₁ 0 = ![0, -1, 0] := by
  simp only [reciprocalXYZ, reciprocalH, mul_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), add_zero, sub_zero, zero_mul, one_mul, neg_mul]

/-- The reciprocal secant equation implies the second relation on its open. -/
theorem reciprocal_secant_relation {x₁ x₂ y₁ y₂ m : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hu : IsUnit (y₁ - y₂)) (hm : m * (y₁ - y₂) = x₁ - x₂) :
    m * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) =
      y₁ + y₂ + W.a₁ * x₂ + W.a₃ := by
  apply hu.mul_left_inj.mp
  linear_combination
    (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) * hm -
      equation_difference W h₁ h₂

/-- The reciprocal tangent equation implies the line relation on its open. -/
theorem reciprocal_tangent_relation {x₁ x₂ y₁ y₂ m : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hu : IsUnit
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁))
    (hm : m *
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) =
      y₁ + y₂ + W.a₁ * x₂ + W.a₃) :
    m * (y₁ - y₂) = x₁ - x₂ := by
  apply hu.mul_left_inj.mp
  linear_combination (y₁ - y₂) * hm + equation_difference W h₁ h₂

/-- The polynomial reciprocal-slope relations imply the homogeneous cubic. -/
theorem equation_reciprocalXYZ {x₁ x₂ y₁ y₂ m : R}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (hl : m * (y₁ - y₂) = x₁ - x₂)
    (hc : m *
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) =
      y₁ + y₂ + W.a₁ * x₂ + W.a₃) :
    W.toProjective.Equation (reciprocalXYZ W x₁ x₂ y₁ m) := by
  rw [Projective.equation_iff]
  rw [Affine.equation_iff] at h₁
  simp only [reciprocalXYZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  dsimp only [reciprocalH]
  linear_combination m ^ 9 * h₁ +
    m ^ 5 * (1 + W.a₁ * m - (W.a₂ + 2 * x₁ + x₂) * m ^ 2) * (hl - m * hc)

end FLT.Mazur.WeierstrassIntegralAddition
