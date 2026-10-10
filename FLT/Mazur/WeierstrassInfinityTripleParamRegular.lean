/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLinearParameterRegular
public import FLT.Mazur.WeierstrassInfinityTripleParamPolynomials

/-!
# Regularity of all actual factors in common centered parameters

Every input factor and every actual output factor is regular in any of the four
common parameter systems. These are polynomial statements; no claim is made
about regularity of their values at points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Each common parameter matrix has determinant one in the actual section ring. -/
theorem infinityTripleParam_determinant (j : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    (-(1 + A.a₃ * infinityTripleLineIntercept W hΔ j)) *
        infinityTripleNegY W hΔ (infinityTripleOutputIndex j) -
      infinityTripleScalarX W hΔ (infinityTripleOutputIndex j) *
        (A.a₁ + A.a₃ * infinityTripleScalarSlope W hΔ j) = 1 :=
  infinity_negated_line_determinant _ (infinityTripleNegLineResidual_output W hΔ j)

/-- All seven transformed input factors are regular, for every choice of center. -/
theorem infinityTripleParamInputPolynomial_regular (j : Fin 4) (i : Fin 7) :
    IsRegular (infinityTripleParamInputPolynomial W hΔ j i) := by
  simpa only [infinityTripleParamInputPolynomial, infinityTripleParamXPolynomial,
    infinityTripleParamYPolynomial, map_neg] using
    infinity_linear_parameter_input_regular (infinityTripleParam_determinant W hΔ j)
      (infinityTripleScalarX W hΔ i)

/-- All four actual output factors are regular in any common parameter system. -/
theorem infinityTripleParamThirdPolynomial_regular (j k : Fin 4) :
    IsRegular (infinityTripleParamThirdPolynomial W hΔ j (infinityTripleOutputIndex k)) := by
  simpa only [infinityTripleParamThirdPolynomial, infinityTripleParamXPolynomial,
    infinityTripleParamYPolynomial, infinityTripleNegY, infinityTripleLineIntercept, map_neg]
    using infinity_linear_parameter_regular (infinityTripleParam_determinant W hΔ j)
      (infinityTripleScalar_third_unimodular W hΔ k)

/-- A transformed input can be canceled in polynomial equations over this section ring. -/
theorem infinityTripleParamInputPolynomial_cancel (j : Fin 4) (i : Fin 7)
    (p q : Γ(InfinityTripleFull W hΔ, ⊤)[X]) :
    infinityTripleParamInputPolynomial W hΔ j i * p =
      infinityTripleParamInputPolynomial W hΔ j i * q ↔ p = q :=
  (infinityTripleParamInputPolynomial_regular W hΔ j i).left.eq_iff

/-- The opposite outer factor can be canceled while retaining the common center. -/
theorem infinityTripleParamThirdPolynomial_cancel (j k : Fin 4)
    (p q : Γ(InfinityTripleFull W hΔ, ⊤)[X]) :
    infinityTripleParamThirdPolynomial W hΔ j (infinityTripleOutputIndex k) * p =
      infinityTripleParamThirdPolynomial W hΔ j (infinityTripleOutputIndex k) * q ↔ p = q :=
  (infinityTripleParamThirdPolynomial_regular W hΔ j k).left.eq_iff

end FLT.Mazur.WeierstrassIntegralChart
