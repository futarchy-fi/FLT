/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityCubicResidualCoefficients

/-!
# Weighted coefficient extraction from a residual syzygy

The determinant-one input parameters supply weights for the three quadratic
coefficients. Applying those weights to the full syzygy gives a scalar
certificate, including the shift introduced by multiplication by X.
-/

@[expose] public section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

variable {S : Type*} [CommRing S]

/-- The coefficient combination used by the primitive input-pair certificate. -/
def infinityQuadraticWeight (n v : S) (P : S[X]) : S :=
  v ^ 2 * P.coeff 0 - n * v * P.coeff 1 + n ^ 2 * P.coeff 2

/-- Weighted extraction retains every coefficient of the shifted quadratic defect. -/
theorem infinityQuadraticWeight_syzygy (n v e m : S) (P H B : S[X])
    (h : C m * P + H * (X - C m) = C e * B) :
    m * infinityQuadraticWeight n v P = e * infinityQuadraticWeight n v B +
      n * v * H.coeff 0 - n ^ 2 * H.coeff 1 + m * infinityQuadraticWeight n v H := by
  have he : C m * P + H * X - C m * H = C e * B := by
    linear_combination h
  have h₀ := congrArg (fun p => p.coeff 0) he
  have h₁ := congrArg (fun p => p.coeff (0 + 1)) he
  have h₂ := congrArg (fun p => p.coeff (1 + 1)) he
  simp only [coeff_add, coeff_sub, mul_coeff_zero, coeff_C_zero, coeff_X_zero,
    mul_zero, add_zero] at h₀
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_mul_X] at h₁ h₂
  unfold infinityQuadraticWeight
  linear_combination v ^ 2 * h₀ - n * v * h₁ + n ^ 2 * h₂

end FLT.Mazur.WeierstrassIntegralChart
