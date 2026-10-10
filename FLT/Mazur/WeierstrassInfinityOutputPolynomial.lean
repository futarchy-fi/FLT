/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityOutputParameter

/-!
# A regular polynomial at the actual normalized output

Base change to the polynomial algebra retains equality of polynomials over
arbitrary rings. The third factor is X, and both transformed input factors
remain regular. Cancellation is used only in this polynomial ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f : InfinityAdditionOpen W →ₐ[R] S)

/-- The cubic on the negated input line, with parameter zero at the actual output. -/
def infinitySpecializationOutputPolynomial : S[X] :=
  let A := W.map (algebraMap R S)
  let m := f (infinityChartSlope W)
  let b := f (infinityInputLeft W (coord W 1 2)) -
    m * f (infinityInputLeft W (coord W 1 0))
  MvPolynomial.eval ![-C (1 + A.a₃ * b) * X +
    C (f (infinityAdditionChart W (coord W 1 0))), 1,
    C (A.a₁ * b - m) * X + C (f (infinityAdditionChart W (coord W 1 2)))]
    (W.map (algebraMap R S[X])).toProjective.polynomial

/-- The transformed factor of an input with normalized X coordinate `a`. -/
def infinitySpecializationOutputInputPolynomial (a : S) : S[X] :=
  let A := W.map (algebraMap R S)
  let m := f (infinityChartSlope W)
  let b := f (infinityInputLeft W (coord W 1 2)) -
    m * f (infinityInputLeft W (coord W 1 0))
  let u := f (infinityAdditionChart W (coord W 1 0))
  let v := f (infinityAdditionChart W (coord W 1 2))
  (-C (1 + A.a₃ * b)) * X + C u -
    C a * (C (A.a₁ + A.a₃ * m) * X + C (-1 - A.a₁ * u - A.a₃ * v))

/-- The output parameter cubic has a simple last factor X as a polynomial identity. -/
theorem infinitySpecializationOutputPolynomial_eq :
    infinitySpecializationOutputPolynomial W f =
      C (f (infinityOutputRestriction W (infinityOutputCoordinates W 1))) *
        infinitySpecializationOutputInputPolynomial W f
          (f (infinityInputLeft W (coord W 1 0))) *
        infinitySpecializationOutputInputPolynomial W f
          (f (infinityInputRight W (coord W 1 0))) * X := by
  have h := infinitySpecialization_output_parameter W
    ((CAlgHom (R := R)).comp f) X 1
  simpa only [infinitySpecializationOutputPolynomial,
    infinitySpecializationOutputInputPolynomial, AlgHom.comp_apply, CAlgHom_apply,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, Polynomial.algebraMap_apply,
    map_sub, map_add, map_neg, map_one, map_mul, mul_one] using h

/-- Every transformed input factor is a non-zero-divisor. -/
theorem infinitySpecializationOutputInputPolynomial_regular (a : S) :
    IsRegular (infinitySpecializationOutputInputPolynomial W f a) := by
  have h := infinity_output_input_regular _ (infinitySpecialization_negated_line W f) a
  convert h using 1
  simp only [infinitySpecializationOutputInputPolynomial, map_sub, map_add, map_neg,
    map_one, map_mul]
  ring

/-- The complete transformed cubic remains regular over an arbitrary coefficient algebra. -/
theorem infinitySpecializationOutputPolynomial_regular :
    IsRegular (infinitySpecializationOutputPolynomial W f) := by
  rw [infinitySpecializationOutputPolynomial_eq]
  exact ((((infinityOutputY_isUnit W).map f).map C).isRegular.mul
    (infinitySpecializationOutputInputPolynomial_regular W f _)).mul
      (infinitySpecializationOutputInputPolynomial_regular W f _) |>.mul monic_X.isRegular

/-- A comparison may cancel this cubic before any evaluation of the parameter. -/
theorem infinitySpecializationOutputPolynomial_cancel (p q : S[X]) :
    infinitySpecializationOutputPolynomial W f * p =
      infinitySpecializationOutputPolynomial W f * q ↔ p = q :=
  (infinitySpecializationOutputPolynomial_regular W f).left.eq_iff

end FLT.Mazur.WeierstrassIntegralChart
