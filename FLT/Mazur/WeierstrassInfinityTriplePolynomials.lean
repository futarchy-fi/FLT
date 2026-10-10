/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleOuterPencils
public import FLT.Mazur.WeierstrassInfinityLinePolynomial

/-!
# Eliminating both inner factors from the four actual line cubics

The three common-center pencils give one comparison of the two outer cubic
polynomials. All quantities are constructed from the genuine full-cover member;
no equality of its outer outputs is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The monic factor belonging to one of the seven actual points. -/
def infinityTriplePointPolynomial (i : Fin 7) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  X - C (infinityTripleScalarX W hΔ i)

/-- The homogeneous factor belonging to the negation of an actual point. -/
def infinityTripleThirdPolynomial (i : Fin 7) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  C (-1 - V.a₁ * infinityTripleScalarX W hΔ i -
      V.a₃ * infinityTripleScalarZ W hΔ i) * X - C (infinityTripleScalarX W hΔ i)

/-- The line cubic of one of the four actual additions. -/
def infinityTripleLinePolynomial (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  infinitySpecializationLinePolynomial W (infinityTripleScalarLaw W hΔ j)

/-- The quadratic correction between two slopes at a specified actual input. -/
def infinityTriplePencilPolynomial (i : Fin 7) (j k : Fin 4) :
    Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  let x := infinityTripleScalarX W hΔ i
  let z := infinityTripleScalarZ W hΔ i
  let l := infinityTripleScalarSlope W hΔ j
  let m := infinityTripleScalarSlope W hΔ k
  C (l - m) * infinitySlopeDenominator (V.map C) X
    (C z + C l * (X - C x)) (C z + C m * (X - C x))

/-- Every actual line polynomial has its two input factors and its normalized third factor. -/
theorem infinityTripleLinePolynomial_eq (j : Fin 4) :
    infinityTripleLinePolynomial W hΔ j =
      C (infinityTripleScalarScale W hΔ j) *
        infinityTriplePointPolynomial W hΔ (infinityTripleLeftIndex j) *
        infinityTriplePointPolynomial W hΔ (infinityTripleRightIndex j) *
        infinityTripleThirdPolynomial W hΔ (infinityTripleOutputIndex j) := by
  simpa only [infinityTripleLinePolynomial, infinityTriplePointPolynomial,
    infinityTripleThirdPolynomial, infinityTripleScalarScale, infinityTripleScalarX,
    infinityTripleScalarZ, infinityTripleScalarLaw_left_coord,
    infinityTripleScalarLaw_right_coord, infinityTripleScalarLaw_output_coord] using
    infinitySpecializationLinePolynomial_eq W (infinityTripleScalarLaw W hΔ j)

/-- Each actual line cubic remains a non-zero-divisor over the common section ring. -/
theorem infinityTripleLinePolynomial_regular (j : Fin 4) :
    IsRegular (infinityTripleLinePolynomial W hΔ j) :=
  infinitySpecializationLinePolynomial_regular W (infinityTripleScalarLaw W hΔ j)

/-- The Q-centered identity in the common polynomial notation. -/
theorem infinityTriplePencilPolynomial_inner :
    C (infinityTripleScalarScale W hΔ 0) * infinityTriplePointPolynomial W hΔ 0 *
        infinityTripleThirdPolynomial W hΔ 3 -
      C (infinityTripleScalarScale W hΔ 1) * infinityTriplePointPolynomial W hΔ 2 *
        infinityTripleThirdPolynomial W hΔ 4 = infinityTriplePencilPolynomial W hΔ 1 0 1 :=
  infinityTripleScalar_inner_pencil_polynomial W hΔ

/-- The R-centered identity in the common polynomial notation. -/
theorem infinityTriplePencilPolynomial_left :
    C (infinityTripleScalarScale W hΔ 2) * infinityTriplePointPolynomial W hΔ 3 *
        infinityTripleThirdPolynomial W hΔ 5 -
      C (infinityTripleScalarScale W hΔ 1) * infinityTriplePointPolynomial W hΔ 1 *
        infinityTripleThirdPolynomial W hΔ 4 = infinityTriplePencilPolynomial W hΔ 2 2 1 :=
  infinityTripleScalar_left_outer_pencil W hΔ

/-- The P-centered identity in the common polynomial notation. -/
theorem infinityTriplePencilPolynomial_right :
    C (infinityTripleScalarScale W hΔ 0) * infinityTriplePointPolynomial W hΔ 1 *
        infinityTripleThirdPolynomial W hΔ 3 -
      C (infinityTripleScalarScale W hΔ 3) * infinityTriplePointPolynomial W hΔ 4 *
        infinityTripleThirdPolynomial W hΔ 6 = infinityTriplePencilPolynomial W hΔ 0 0 3 :=
  infinityTripleScalar_right_outer_pencil W hΔ

/-- Eliminate both inner third factors to compare the two actual outer cubic polynomials. -/
theorem infinityTripleLinePolynomial_outer_sub :
    infinityTripleLinePolynomial W hΔ 2 - infinityTripleLinePolynomial W hΔ 3 =
      infinityTriplePointPolynomial W hΔ 2 * infinityTriplePencilPolynomial W hΔ 2 2 1 +
        infinityTriplePointPolynomial W hΔ 0 * infinityTriplePencilPolynomial W hΔ 0 0 3 -
        infinityTriplePointPolynomial W hΔ 1 * infinityTriplePencilPolynomial W hΔ 1 0 1 := by
  rw [infinityTripleLinePolynomial_eq, infinityTripleLinePolynomial_eq]
  change C (infinityTripleScalarScale W hΔ 2) * infinityTriplePointPolynomial W hΔ 3 *
      infinityTriplePointPolynomial W hΔ 2 * infinityTripleThirdPolynomial W hΔ 5 -
    C (infinityTripleScalarScale W hΔ 3) * infinityTriplePointPolynomial W hΔ 0 *
      infinityTriplePointPolynomial W hΔ 4 * infinityTripleThirdPolynomial W hΔ 6 = _
  linear_combination
    infinityTriplePointPolynomial W hΔ 2 * infinityTriplePencilPolynomial_left W hΔ +
    infinityTriplePointPolynomial W hΔ 0 * infinityTriplePencilPolynomial_right W hΔ -
    infinityTriplePointPolynomial W hΔ 1 * infinityTriplePencilPolynomial_inner W hΔ

end FLT.Mazur.WeierstrassIntegralChart
