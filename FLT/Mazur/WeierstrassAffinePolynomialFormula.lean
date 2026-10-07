/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalAdditionFormula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

/-!
# Integral comparison of polynomial and affine addition formulas

The homogeneous polynomial law is the ordinary slope law scaled by the cube
of the x-difference, or the reciprocal slope law scaled by the cube of the
y-difference. The identities hold over rings with zero divisors.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x₁ x₂ y₁ y₂ : R}
  (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)

include h₁ h₂

/-- The polynomial z-coordinate on affine inputs is the cube of their x-difference. -/
theorem affinePolynomial_z :
    W.toProjective.addZ ![x₁, y₁, 1] ![x₂, y₂, 1] = (x₁ - x₂) ^ 3 := by
  simpa only [Projective.fin3_def_ext, mul_one] using
    Projective.addZ_eq' ((Projective.equation_some ..).mpr h₁)
      ((Projective.equation_some ..).mpr h₂)

/-- The polynomial x-coordinate in terms of the two affine differences. -/
theorem affinePolynomial_x :
    W.toProjective.addX ![x₁, y₁, 1] ![x₂, y₂, 1] =
      ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) * (x₁ - x₂) := by
  have h := Projective.addX_eq' ((Projective.equation_some ..).mpr h₁)
    ((Projective.equation_some ..).mpr h₂)
  simp only [Projective.fin3_def_ext, mul_one, one_pow] at h
  rw [h]
  ring

/-- The polynomial third-intersection y-coordinate in terms of affine differences. -/
theorem affinePolynomial_negY :
    W.toProjective.negAddY ![x₁, y₁, 1] ![x₂, y₂, 1] =
      (y₁ - y₂) * ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + 2 * x₁ + x₂) * (x₁ - x₂) ^ 2) + y₁ * (x₁ - x₂) ^ 3 := by
  have h := Projective.negAddY_eq' ((Projective.equation_some ..).mpr h₁)
    ((Projective.equation_some ..).mpr h₂)
  simp only [Projective.fin3_def_ext, mul_one, one_pow] at h
  rw [h]
  ring

/-- Any ordinary slope satisfying the line relation gives the same homogeneous law. -/
theorem affinePolynomial_ordinary {l : R} (hl : l * (x₁ - x₂) = y₁ - y₂) :
    W.toProjective.addXYZ ![x₁, y₁, 1] ![x₂, y₂, 1] =
      (x₁ - x₂) ^ 3 •
        ![W.toAffine.addX x₁ x₂ l, W.toAffine.addY x₁ x₂ y₁ l, 1] := by
  ext i
  fin_cases i <;>
    simp only [Projective.addXYZ, Projective.addY, Projective.negY,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, affinePolynomial_x W h₁ h₂,
      affinePolynomial_negY W h₁ h₂, affinePolynomial_z W h₁ h₂,
      ← hl, Affine.addX, Affine.addY, Affine.negY, Affine.negAddY] <;> dsimp <;> ring

/-- A reciprocal slope gives the same polynomial law even when the slope vanishes. -/
theorem affinePolynomial_reciprocal {m : R} (hm : m * (y₁ - y₂) = x₁ - x₂) :
    W.toProjective.addXYZ ![x₁, y₁, 1] ![x₂, y₂, 1] =
      (y₁ - y₂) ^ 3 • reciprocalXYZ W x₁ x₂ y₁ m := by
  ext i
  fin_cases i <;>
    simp only [Projective.addXYZ, Projective.addY, Projective.negY,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, affinePolynomial_x W h₁ h₂,
      affinePolynomial_negY W h₁ h₂, affinePolynomial_z W h₁ h₂,
      ← hm, reciprocalXYZ, reciprocalH] <;> dsimp <;> ring

end FLT.Mazur.WeierstrassIntegralChart
