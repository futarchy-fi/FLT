/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinitySpecializedFactorization
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Cancellation of the actual third-point polynomial

Its two coefficients generate the unit ideal. McCoy's theorem therefore makes
the polynomial a non-zero-divisor, even over a nonreduced coefficient algebra
and without inverting its leading coefficient.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial nonZeroDivisors

variable {S : Type*} [CommRing S]

/-- A linear polynomial with a displayed coefficient Bezout identity is regular. -/
theorem infinityLinear_mem_nonZeroDivisors {n x a b : S} (h : n * a + x * b = 1) :
    C n * X - C x ∈ S[X]⁰ := by
  apply Polynomial.mem_nonZeroDivisors_iff.mpr
  intro r hr
  have hn : r * n = 0 := by
    simpa using congrArg (fun p : S[X] => p.coeff 1) hr
  have hx : r * x = 0 := by
    have he := congrArg (fun p : S[X] => p.coeff 0) hr
    simpa using he
  linear_combination a * hn + b * hx - r * h

variable {R : Type*} [CommRing R] [Algebra R S]
  (W : WeierstrassCurve R) (f : InfinityAdditionOpen W →ₐ[R] S)

/-- The negated actual output defines a regular last factor in the split line cubic. -/
theorem infinitySpecialization_factor_regular :
    let V := W.map (algebraMap R S)
    let x := f (infinityAdditionChart W (coord W 1 0))
    let z := f (infinityAdditionChart W (coord W 1 2))
    C (-1 - V.a₁ * x - V.a₃ * z) * X - C x ∈ S[X]⁰ :=
  infinityLinear_mem_nonZeroDivisors (infinitySpecialization_third_unimodular W f)

/-- The genuine third factor can be canceled from a polynomial comparison. -/
theorem infinitySpecialization_factor_cancel (p q : S[X]) :
    let V := W.map (algebraMap R S)
    let x := f (infinityAdditionChart W (coord W 1 0))
    let z := f (infinityAdditionChart W (coord W 1 2))
    let c := C (-1 - V.a₁ * x - V.a₃ * z) * X - C x
    c * p = c * q ↔ p = q :=
  (isRegular_iff_mem_nonZeroDivisors.mpr
    (infinitySpecialization_factor_regular W f)).left.eq_iff

end FLT.Mazur.WeierstrassIntegralChart
