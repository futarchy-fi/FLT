/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleParamCoefficients

/-!
# Reciprocity between the two actual cross-line residuals

The two own-line equations express the opposite residual through the first
residual and the point minor. This retains the nonlinear a₃ term and does not
require either negated Y coordinate to be invertible.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

section Scalar

variable {S : Type*} [CommRing S] (A : WeierstrassCurve S)

/-- Two normalized points on their own negated lines satisfy an exact residual reciprocity. -/
theorem infinity_negated_line_residual_reciprocity {u v x z m b r c : S}
    (hu : v - m * u - b * (-1 - A.a₁ * u - A.a₃ * v) = 0)
    (hx : z - r * x - c * (-1 - A.a₁ * x - A.a₃ * z) = 0) :
    let n := -1 - A.a₁ * u - A.a₃ * v
    let t := -1 - A.a₁ * x - A.a₃ * z
    let e := z - m * x - b * t
    let f := v - r * u - c * n
    let a := -(1 + A.a₃ * b) * (m - r) + (A.a₁ + A.a₃ * m) * (b - c)
    e + f + A.a₃ * e * f + a * (n * x - u * t) = 0 := by
  dsimp only
  linear_combination
    (1 + A.a₃ * (z - r * x - c * (-1 - A.a₁ * x - A.a₃ * z))) * hu + hx

end Scalar

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The linear coefficient of the separation of two actual lines centered at the first output. -/
def infinityTripleLineSeparationSlope (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  (-(1 + A.a₃ * infinityTripleLineIntercept W hΔ j)) *
      (infinityTripleScalarSlope W hΔ j - infinityTripleScalarSlope W hΔ k) +
    (A.a₁ + A.a₃ * infinityTripleScalarSlope W hΔ j) *
      (infinityTripleLineIntercept W hΔ j - infinityTripleLineIntercept W hΔ k)

/-- Line separation has precisely the cross residual as its constant coefficient. -/
theorem infinityTripleParamLineZPolynomial_separation (j k : Fin 4) :
    infinityTripleParamLineZPolynomial W hΔ j j -
        infinityTripleParamLineZPolynomial W hΔ j k =
      C (infinityTripleLineSeparationSlope W hΔ j k) * X +
        C (infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k) := by
  have h := congrArg (C : Γ(InfinityTripleFull W hΔ, ⊤) →+*
    Γ(InfinityTripleFull W hΔ, ⊤)[X]) (infinityTripleNegLineResidual_output W hΔ j)
  unfold infinityTripleNegLineResidual at h
  unfold infinityTripleParamLineZPolynomial infinityTripleParamXPolynomial
    infinityTripleParamYPolynomial infinityTripleLineSeparationSlope infinityTripleNegLineResidual
  simp only [map_add, map_sub, map_neg, map_mul, map_one, map_zero] at h ⊢
  linear_combination -h

/-- The two actual cross residuals are linked by the genuine output minor. -/
theorem infinityTripleNegLineResidual_reciprocity (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
    e + f + A.a₃ * e * f + infinityTripleLineSeparationSlope W hΔ j k *
      infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) (infinityTripleOutputIndex k) =
        0 :=
  infinity_negated_line_residual_reciprocity _
    (infinityTripleNegLineResidual_output W hΔ j) (infinityTripleNegLineResidual_output W hΔ k)

/-- The product of the two leading coefficients differs from one by the minor term. -/
theorem infinityTripleParamThirdPolynomial_leading_product (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    (infinityTripleParamThirdPolynomial W hΔ j (infinityTripleOutputIndex k)).coeff 1 *
        (infinityTripleParamThirdPolynomial W hΔ k (infinityTripleOutputIndex j)).coeff 1 +
      A.a₃ * infinityTripleLineSeparationSlope W hΔ j k *
        infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) (infinityTripleOutputIndex k) =
          1 := by
  rw [infinityTripleParamThirdPolynomial_coeff_one, infinityTripleParamThirdPolynomial_coeff_one]
  dsimp only
  linear_combination
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))).a₃ *
      infinityTripleNegLineResidual_reciprocity W hΔ j k

end FLT.Mazur.WeierstrassIntegralChart
