/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFactorCancellation

/-!
# The actual infinity line cubic as a regular polynomial

Specializing into the polynomial algebra upgrades scalar evaluations to an
identity of polynomials. All three linear factors are regular; consequently
the line cubic itself can be canceled over arbitrary coefficient rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f : InfinityAdditionOpen W →ₐ[R] S)

/-- The Weierstrass cubic restricted to the actual input line, in the polynomial algebra. -/
def infinitySpecializationLinePolynomial : S[X] :=
  MvPolynomial.eval ![X, 1, C (f (infinityChartSlope W)) * X +
    C (f (infinityInputLeft W (coord W 1 2)) -
      f (infinityChartSlope W) * f (infinityInputLeft W (coord W 1 0)))]
    (W.map (algebraMap R S[X])).toProjective.polynomial

/-- The actual line cubic splits as a polynomial, not only as a function on the base ring. -/
theorem infinitySpecializationLinePolynomial_eq :
    let V := W.map (algebraMap R S)
    let x := f (infinityAdditionChart W (coord W 1 0))
    let z := f (infinityAdditionChart W (coord W 1 2))
    infinitySpecializationLinePolynomial W f =
      C (f (infinityOutputRestriction W (infinityOutputCoordinates W 1))) *
        (X - C (f (infinityInputLeft W (coord W 1 0)))) *
        (X - C (f (infinityInputRight W (coord W 1 0)))) *
        (C (-1 - V.a₁ * x - V.a₃ * z) * X - C x) := by
  have h := infinitySpecialization_factorization W
    ((CAlgHom (R := R)).comp f) X 1
  simpa only [infinitySpecializationLinePolynomial, AlgHom.comp_apply, CAlgHom_apply,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, Polynomial.algebraMap_apply,
    map_sub, map_neg, map_one, map_mul, mul_one] using h

/-- The whole input-line cubic is regular without any leading-coefficient unit assumption. -/
theorem infinitySpecializationLinePolynomial_regular :
    IsRegular (infinitySpecializationLinePolynomial W f) := by
  rw [infinitySpecializationLinePolynomial_eq]
  exact ((((infinityOutputY_isUnit W).map f).map C).isRegular.mul
    (monic_X_sub_C _).isRegular).mul (monic_X_sub_C _).isRegular |>.mul
      (isRegular_iff_mem_nonZeroDivisors.mpr (infinitySpecialization_factor_regular W f))

/-- Polynomial comparisons may cancel the actual line cubic even over nonreduced rings. -/
theorem infinitySpecializationLinePolynomial_cancel (p q : S[X]) :
    infinitySpecializationLinePolynomial W f * p =
        infinitySpecializationLinePolynomial W f * q ↔ p = q :=
  (infinitySpecializationLinePolynomial_regular W f).left.eq_iff

end FLT.Mazur.WeierstrassIntegralChart
