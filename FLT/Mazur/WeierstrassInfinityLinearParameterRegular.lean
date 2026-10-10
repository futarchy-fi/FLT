/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFactorCancellation

/-!
# Regular linear factors under a determinant-one parameter change

A unimodular pair of coefficients stays unimodular under the common change of
parameters. The argument works over rings with zero divisors and requires no
unit leading coefficient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial nonZeroDivisors

variable {R : Type*} [CommRing R]

/-- The inverse matrix transports a displayed coefficient Bezout identity. -/
theorem infinity_linear_parameter_bezout {a b c d n x r s : R}
    (hd : a * d - b * c = 1) (hn : n * r + x * s = 1) :
    (n * a - x * c) * (d * r + b * s) +
      (n * b - x * d) * (-c * r - a * s) = 1 := by
  linear_combination (n * r + x * s) * hd + hn

/-- A common invertible parameter change preserves regularity of a unimodular factor. -/
theorem infinity_linear_parameter_regular {a b c d n x r s : R}
    (hd : a * d - b * c = 1) (hn : n * r + x * s = 1) :
    IsRegular (C n * (C a * X + C b) - C x * (C c * X + C d)) := by
  have h := infinityLinear_mem_nonZeroDivisors
    (n := n * a - x * c) (x := -(n * b - x * d))
    (a := d * r + b * s) (b := c * r + a * s)
    (by linear_combination infinity_linear_parameter_bezout hd hn)
  convert isRegular_iff_mem_nonZeroDivisors.mpr h using 1
  simp only [map_sub, map_mul, map_neg]
  ring

/-- An input factor remains regular in these same parameters. -/
theorem infinity_linear_parameter_input_regular {a b c d : R}
    (hd : a * d - b * c = 1) (x : R) :
    IsRegular ((C a * X + C b) - C x * (C c * X + C d)) := by
  simpa only [map_one, one_mul] using
    infinity_linear_parameter_regular (n := 1) (r := 1) (s := 0) hd (by ring)

/-- Regular transformed factors can be canceled before evaluating the parameter. -/
theorem infinity_linear_parameter_cancel {a b c d n x r s : R}
    (hd : a * d - b * c = 1) (hn : n * r + x * s = 1) (p q : R[X]) :
    (C n * (C a * X + C b) - C x * (C c * X + C d)) * p =
      (C n * (C a * X + C b) - C x * (C c * X + C d)) * q ↔ p = q :=
  (infinity_linear_parameter_regular hd hn).left.eq_iff

end FLT.Mazur.WeierstrassIntegralChart
