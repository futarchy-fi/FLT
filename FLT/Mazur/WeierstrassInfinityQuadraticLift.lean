/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityCubicDifference
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Homogeneous evaluation of the quadratic secant pencil

Extracting coefficients before homogeneous evaluation works over arbitrary rings.
In particular it does not infer polynomial equality from finitely many values,
and does not require the homogeneous Y coordinate to be invertible.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial

variable {R : Type*} [CommRing R]

/-- Homogeneous evaluation of the degree-two part, retaining lower coefficients. -/
def infinityQuadraticLift (p : R[X]) (U V : R) : R :=
  p.coeff 2 * U ^ 2 + p.coeff 1 * U * V + p.coeff 0 * V ^ 2

/-- Homogeneous evaluation respects subtraction. -/
theorem infinityQuadraticLift_sub (p q : R[X]) (U V : R) :
    infinityQuadraticLift (p - q) U V =
      infinityQuadraticLift p U V - infinityQuadraticLift q U V := by
  simp only [infinityQuadraticLift, coeff_sub]
  ring

/-- Constant factors pass through homogeneous evaluation. -/
theorem infinityQuadraticLift_C_mul (c : R) (p : R[X]) (U V : R) :
    infinityQuadraticLift (C c * p) U V = c * infinityQuadraticLift p U V := by
  simp only [infinityQuadraticLift, coeff_C_mul]
  ring

/-- A pair of linear factors homogenizes with no assumptions on its leading coefficients. -/
theorem infinityQuadraticLift_factors (a n u U V : R) :
    infinityQuadraticLift ((X - C a) * (C n * X - C u)) U V =
      (U - a * V) * (n * U - u * V) := by
  have h : (X - C a) * (C n * X - C u) =
      C n * X ^ 2 - C (u + a * n) * X + C (a * u) := by
    simp only [map_add, map_mul]
    ring
  rw [h]
  simp [infinityQuadraticLift, coeff_C_mul]
  ring

/-- The divided cubic denominator homogenizes to the genuine homogeneous quadratic. -/
theorem infinityQuadraticLift_denominator (W : WeierstrassCurve R) (x z l m U V : R) :
    infinityQuadraticLift (infinitySlopeDenominator (W.map C) X
      (C z + C l * (X - C x)) (C z + C m * (X - C x))) U V =
      infinityCubicDividedZ W U V (z * V + l * (U - x * V))
        (z * V + m * (U - x * V)) := by
  simp [infinityQuadraticLift, infinitySlopeDenominator, infinityCubicDividedZ,
    pow_two, coeff_mul, coeff_one, coeff_X, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  ring

end FLT.Mazur.WeierstrassIntegralChart
