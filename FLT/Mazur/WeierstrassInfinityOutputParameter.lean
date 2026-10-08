/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineParameter
public import FLT.Mazur.WeierstrassInfinityFactorCancellation

/-!
# The actual infinity cubic in parameters centered at its output

An invertible parameter change makes the third factor U and keeps both input
factors regular as polynomials. It does not invert the old third point's Y
coordinate or specialize a polynomial cancellation to a scalar cancellation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial nonZeroDivisors

variable {S : Type*} [CommRing S] (A : WeierstrassCurve S)

/-- Every transformed input factor has an explicit coefficient Bezout identity. -/
theorem infinity_output_input_bezout {u v m b : S}
    (h : v - m * u - b * (-1 - A.a₁ * u - A.a₃ * v) = 0) (a : S) :
    let n := -1 - A.a₁ * u - A.a₃ * v
    let q := A.a₁ + A.a₃ * m
    (-(1 + A.a₃ * b) - a * q) * n - (u - a * n) * q = 1 := by
  dsimp only
  linear_combination infinity_negated_line_determinant A h

/-- The transformed input factors are regular even if neither coefficient is a unit. -/
theorem infinity_output_input_regular {u v m b : S}
    (h : v - m * u - b * (-1 - A.a₁ * u - A.a₃ * v) = 0) (a : S) :
    let n := -1 - A.a₁ * u - A.a₃ * v
    let q := A.a₁ + A.a₃ * m
    IsRegular (C (-(1 + A.a₃ * b) - a * q) * X + C (u - a * n)) := by
  dsimp only
  have hB := infinity_output_input_bezout A h a
  dsimp only at hB
  have hR := infinityLinear_mem_nonZeroDivisors
    (n := -(1 + A.a₃ * b) - a * (A.a₁ + A.a₃ * m))
    (x := -(u - a * (-1 - A.a₁ * u - A.a₃ * v)))
    (a := -1 - A.a₁ * u - A.a₃ * v) (b := A.a₁ + A.a₃ * m)
    (by linear_combination hB)
  simpa only [map_neg, sub_neg_eq_add] using isRegular_iff_mem_nonZeroDivisors.mpr hR

variable {R : Type*} [CommRing R] [Algebra R S]
  (W : WeierstrassCurve R) (f : InfinityAdditionOpen W →ₐ[R] S)

/-- The actual normalized output gives the line relation needed by the parameter change. -/
theorem infinitySpecialization_negated_line :
    let A := W.map (algebraMap R S)
    let m := f (infinityChartSlope W)
    let b := f (infinityInputLeft W (coord W 1 2)) -
      m * f (infinityInputLeft W (coord W 1 0))
    let u := f (infinityAdditionChart W (coord W 1 0))
    let v := f (infinityAdditionChart W (coord W 1 2))
    v - m * u - b * (-1 - A.a₁ * u - A.a₃ * v) = 0 := by
  dsimp only
  linear_combination infinitySpecialization_output_line W f

/-- The actual line cubic factors with the output represented by the simple factor U. -/
theorem infinitySpecialization_output_parameter (U V : S) :
    let A := W.map (algebraMap R S)
    let m := f (infinityChartSlope W)
    let b := f (infinityInputLeft W (coord W 1 2)) -
      m * f (infinityInputLeft W (coord W 1 0))
    let u := f (infinityAdditionChart W (coord W 1 0))
    let v := f (infinityAdditionChart W (coord W 1 2))
    let n := -1 - A.a₁ * u - A.a₃ * v
    let X' := -(1 + A.a₃ * b) * U + u * V
    let Y' := (A.a₁ + A.a₃ * m) * U + n * V
    MvPolynomial.eval ![X', V, (A.a₁ * b - m) * U + v * V] A.toProjective.polynomial =
      f (infinityOutputRestriction W (infinityOutputCoordinates W 1)) *
        (X' - f (infinityInputLeft W (coord W 1 0)) * Y') *
        (X' - f (infinityInputRight W (coord W 1 0)) * Y') * U := by
  dsimp only
  rw [infinity_negated_line_parameter_cubic _ (infinitySpecialization_negated_line W f),
    infinitySpecialization_factorization,
    infinity_negated_line_parameter_third _ (infinitySpecialization_negated_line W f)]

end FLT.Mazur.WeierstrassIntegralChart
