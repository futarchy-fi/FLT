/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.LinearCombination

/-!
# Coefficient equations of a centered cubic comparison

Keep the common free parameter when comparing a cubic with third factor X to a
cubic with an arbitrary linear third factor. Extracting all coefficients retains
the tangent information lost by evaluating only at zero.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial

variable {R : Type*} [CommRing R] {P Q D : R[X]} {n m a b : R}

/-- The constant equation of the cubic comparison, without canceling any evaluated factor. -/
theorem infinity_cubic_residual_coeff_zero
    (h : P * X - Q * (C n * X - C m) = (C a * X + C b) * D) :
    Q.coeff 0 * m = b * D.coeff 0 := by
  have hc := congrArg (fun p => p.coeff 0) h
  simpa only [coeff_sub, mul_coeff_zero, coeff_X_zero, coeff_C_zero,
    coeff_add, mul_zero, zero_sub, zero_add, mul_neg, sub_neg_eq_add] using hc

/-- Every higher coefficient supplies its own exact recurrence. -/
theorem infinity_cubic_residual_coeff_succ
    (h : P * X - Q * (C n * X - C m) = (C a * X + C b) * D) (i : ℕ) :
    P.coeff i - n * Q.coeff i + m * Q.coeff (i + 1) =
      a * D.coeff i + b * D.coeff (i + 1) := by
  have he : P * X - C n * (Q * X) + C m * Q = C a * (D * X) + C b * D := by
    linear_combination h
  have hc := congrArg (fun p => p.coeff (i + 1)) he
  simpa only [coeff_add, coeff_sub, coeff_C_mul, coeff_mul_X] using hc

end FLT.Mazur.WeierstrassIntegralChart
