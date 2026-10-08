/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityDividedQuadraticCoefficients
public import FLT.Mazur.WeierstrassInfinityTripleInputPairCoefficients

/-!
# Explicit coefficients of the actual divided correction

All three coefficients are computed in the true section ring. The constant
term is the vertical derivative at the center plus its exact residual correction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The direction coefficient of any actual line in the chosen common parameters. -/
def infinityTripleParamLineDirection (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarSlope W hΔ k * infinityTripleParamDirectionX W hΔ j +
    infinityTripleLineIntercept W hΔ k * infinityTripleParamDirectionY W hΔ j

/-- The own-line direction simplifies without inverting a coordinate. -/
theorem infinityTripleParamLineDirection_self (j : Fin 4) :
    infinityTripleParamLineDirection W hΔ j j =
      (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))).a₁ *
        infinityTripleLineIntercept W hΔ j - infinityTripleScalarSlope W hΔ j := by
  unfold infinityTripleParamLineDirection infinityTripleParamDirectionX
    infinityTripleParamDirectionY
  ring

/-- An actual line has its explicit direction and cross-residual constant. -/
theorem infinityTripleParamLineZPolynomial_linear (j k : Fin 4) :
    infinityTripleParamLineZPolynomial W hΔ j k =
      C (infinityTripleParamLineDirection W hΔ j k) * X +
        C (infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j) -
          infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k) := by
  simp only [infinityTripleParamLineZPolynomial, infinityTripleParamXPolynomial_linear,
    infinityTripleParamYPolynomial_linear, infinityTripleParamLineDirection,
    infinityTripleNegLineResidual, map_sub, map_add, map_mul]
  ring

/-- The own line has the genuine Z coordinate as its constant coefficient. -/
theorem infinityTripleParamLineZPolynomial_self_linear (j : Fin 4) :
    infinityTripleParamLineZPolynomial W hΔ j j =
      C (infinityTripleParamLineDirection W hΔ j j) * X +
        C (infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j)) := by
  rw [infinityTripleParamLineZPolynomial_linear, infinityTripleNegLineResidual_output,
    sub_zero]

/-- The constant coefficient is evaluated at the two actual line values at the center. -/
theorem infinityTripleParamDividedPolynomial_coeff_zero (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let i := infinityTripleOutputIndex j
    (infinityTripleParamDividedPolynomial W hΔ j k).coeff 0 =
      infinityCubicDividedZ A (infinityTripleScalarX W hΔ i) (infinityTripleNegY W hΔ i)
        (infinityTripleScalarZ W hΔ i)
        (infinityTripleScalarZ W hΔ i - infinityTripleNegLineResidual W hΔ i k) := by
  unfold infinityTripleParamDividedPolynomial
  rw [infinityTripleParamXPolynomial_linear, infinityTripleParamYPolynomial_linear,
    infinityTripleParamLineZPolynomial_self_linear, infinityTripleParamLineZPolynomial_linear]
  exact infinityCubicDividedZ_linear_coeff_zero
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))) _ _ _ _ _ _ _ _

/-- The middle coefficient is the explicit integral polarization of direction and center. -/
theorem infinityTripleParamDividedPolynomial_coeff_one (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let i := infinityTripleOutputIndex j
    (infinityTripleParamDividedPolynomial W hΔ j k).coeff 1 =
      infinityDividedZPolar A
        (infinityTripleParamDirectionX W hΔ j) (infinityTripleParamDirectionY W hΔ j)
        (infinityTripleParamLineDirection W hΔ j j)
        (infinityTripleParamLineDirection W hΔ j k)
        (infinityTripleScalarX W hΔ i) (infinityTripleNegY W hΔ i)
        (infinityTripleScalarZ W hΔ i)
        (infinityTripleScalarZ W hΔ i - infinityTripleNegLineResidual W hΔ i k) := by
  unfold infinityTripleParamDividedPolynomial
  rw [infinityTripleParamXPolynomial_linear, infinityTripleParamYPolynomial_linear,
    infinityTripleParamLineZPolynomial_self_linear, infinityTripleParamLineZPolynomial_linear]
  exact infinityCubicDividedZ_linear_coeff_one
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))) _ _ _ _ _ _ _ _

/-- The top coefficient depends only on the directions of the four linear coordinates. -/
theorem infinityTripleParamDividedPolynomial_coeff_two (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    (infinityTripleParamDividedPolynomial W hΔ j k).coeff 2 =
      infinityCubicDividedZ A
        (infinityTripleParamDirectionX W hΔ j) (infinityTripleParamDirectionY W hΔ j)
        (infinityTripleParamLineDirection W hΔ j j)
        (infinityTripleParamLineDirection W hΔ j k) := by
  unfold infinityTripleParamDividedPolynomial
  rw [infinityTripleParamXPolynomial_linear, infinityTripleParamYPolynomial_linear,
    infinityTripleParamLineZPolynomial_self_linear, infinityTripleParamLineZPolynomial_linear]
  exact infinityCubicDividedZ_linear_coeff_two
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))) _ _ _ _ _ _ _ _

/-- The constant coefficient includes the quadratic residual correction, even on a tangent. -/
theorem infinityTripleParamDividedPolynomial_constant_residual (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let i := infinityTripleOutputIndex j
    let x := infinityTripleScalarX W hΔ i
    let y := infinityTripleNegY W hΔ i
    let z := infinityTripleScalarZ W hΔ i
    let f := infinityTripleNegLineResidual W hΔ i k
    (infinityTripleParamDividedPolynomial W hΔ j k).coeff 0 =
      infinityCubicDividedZ A x y z z +
        f * (A.a₄ * x - A.a₃ * y + 3 * A.a₆ * z) - A.a₆ * f ^ 2 := by
  rw [infinityTripleParamDividedPolynomial_coeff_zero, infinityCubicDividedZ_residual]

end FLT.Mazur.WeierstrassIntegralChart
