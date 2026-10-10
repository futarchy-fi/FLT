/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleNegatedPencils
public import FLT.Mazur.WeierstrassInfinityOutputPolynomial

/-!
# Common output parameters for the genuine triple member

Center the line parameters at any of the four actual outputs. The corresponding
third factor becomes U; every other third factor retains its actual point minor
as the coefficient of V. These parameters are defined on the whole member.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The first coordinate in parameters centered at the actual output of law `j`. -/
def infinityTripleOutputParamX (j : Fin 4) (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  (-(1 + A.a₃ * infinityTripleLineIntercept W hΔ j)) * U +
    infinityTripleScalarX W hΔ (infinityTripleOutputIndex j) * V

/-- The old homogeneous Y coordinate in the new output parameters. -/
def infinityTripleOutputParamY (j : Fin 4) (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  (A.a₁ + A.a₃ * infinityTripleScalarSlope W hΔ j) * U +
    infinityTripleNegY W hΔ (infinityTripleOutputIndex j) * V

/-- Any actual input factor in the common output parameters. -/
def infinityTripleOutputParamInput (j : Fin 4) (i : Fin 7)
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleOutputParamX W hΔ j U V -
    infinityTripleScalarX W hΔ i * infinityTripleOutputParamY W hΔ j U V

/-- Any actual third factor in the same common output parameters. -/
def infinityTripleOutputParamThird (j : Fin 4) (i : Fin 7)
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleNegY W hΔ i * infinityTripleOutputParamX W hΔ j U V -
    infinityTripleScalarX W hΔ i * infinityTripleOutputParamY W hΔ j U V

/-- The law's own third factor is precisely the first new coordinate. -/
theorem infinityTripleOutputParamThird_self (j : Fin 4)
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    infinityTripleOutputParamThird W hΔ j (infinityTripleOutputIndex j) U V = U :=
  infinity_negated_line_parameter_third _ (infinityTripleNegLineResidual_output W hΔ j) U V

/-- The constant homogeneous coefficient of any other third factor is its actual minor. -/
theorem infinityTripleOutputParamThird_expand (j : Fin 4) (i : Fin 7)
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    infinityTripleOutputParamThird W hΔ j i U V =
      (-(1 + A.a₃ * infinityTripleLineIntercept W hΔ j) * infinityTripleNegY W hΔ i -
        infinityTripleScalarX W hΔ i * (A.a₁ + A.a₃ * infinityTripleScalarSlope W hΔ j)) * U +
      infinityTripleNegMinor W hΔ i (infinityTripleOutputIndex j) * V := by
  unfold infinityTripleOutputParamThird infinityTripleOutputParamX infinityTripleOutputParamY
    infinityTripleNegMinor
  ring

/-- In the left output's parameters the opposite third factor records the associativity minor. -/
theorem infinityTripleOutputParamThird_outer_zero :
    infinityTripleOutputParamThird W hΔ 2 6 0 1 = -infinityTripleNegMinor W hΔ 5 6 := by
  rw [infinityTripleOutputParamThird_expand]
  simp only [mul_zero, mul_one, zero_add]
  exact infinityTripleNegMinor_swap W hΔ 6 5

/-- Each actual cubic becomes the product of its two transformed inputs and U. -/
theorem infinityTripleOutputParam_factorization (j : Fin 4)
    (U V : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    MvPolynomial.eval ![infinityTripleOutputParamX W hΔ j U V, V,
      (A.a₁ * infinityTripleLineIntercept W hΔ j - infinityTripleScalarSlope W hΔ j) * U +
        infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j) * V]
      A.toProjective.polynomial =
      infinityTripleScalarScale W hΔ j *
        infinityTripleOutputParamInput W hΔ j (infinityTripleLeftIndex j) U V *
        infinityTripleOutputParamInput W hΔ j (infinityTripleRightIndex j) U V * U := by
  simpa only [infinityTripleOutputParamInput, infinityTripleOutputParamX,
    infinityTripleOutputParamY, infinityTripleNegY, infinityTripleScalarScale,
    infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleLineIntercept, infinityTripleScalarLaw_left_coord,
    infinityTripleScalarLaw_right_coord, infinityTripleScalarLaw_output_coord] using
    infinitySpecialization_output_parameter W (infinityTripleScalarLaw W hΔ j) U V

/-- The actual polynomial in these parameters is regular for every one of the four laws. -/
theorem infinityTripleOutputPolynomial_regular (j : Fin 4) :
    IsRegular (infinitySpecializationOutputPolynomial W (infinityTripleScalarLaw W hΔ j)) :=
  infinitySpecializationOutputPolynomial_regular W (infinityTripleScalarLaw W hΔ j)

end FLT.Mazur.WeierstrassIntegralChart
