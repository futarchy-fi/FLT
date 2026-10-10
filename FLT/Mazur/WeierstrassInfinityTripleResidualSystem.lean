/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityCubicResidualCoefficients
public import FLT.Mazur.WeierstrassInfinityTripleResidualReciprocity

/-!
# The actual polynomial system for the two remaining residuals

The comparison includes every coefficient, not just the value at the center.
Its constant equation and reciprocity give an exact linear relation between
the first cross residual and the minor. None of its coefficients is assumed a unit.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The unit scale times both actual input factors of a law in the common parameters. -/
def infinityTripleParamInputPair (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  C (infinityTripleScalarScale W hΔ k) *
    infinityTripleParamInputPolynomial W hΔ j (infinityTripleLeftIndex k) *
    infinityTripleParamInputPolynomial W hΔ j (infinityTripleRightIndex k)

/-- The divided cubic between the center's own line and the comparison line. -/
def infinityTripleParamDividedPolynomial (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  infinityCubicDividedZ (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤)[X]))
    (infinityTripleParamXPolynomial W hΔ j) (infinityTripleParamYPolynomial W hΔ j)
    (infinityTripleParamLineZPolynomial W hΔ j j)
    (infinityTripleParamLineZPolynomial W hΔ j k)

/-- The input-pair polynomial is regular even when its constant coefficient is a zero divisor. -/
theorem infinityTripleParamInputPair_regular (j k : Fin 4) :
    IsRegular (infinityTripleParamInputPair W hΔ j k) :=
  ((((infinityTripleScalar_scale_unit W hΔ k).map C).isRegular.mul
    (infinityTripleParamInputPolynomial_regular W hΔ j _)).mul
      (infinityTripleParamInputPolynomial_regular W hΔ j _))

/-- The full polynomial comparison exposes both cross residuals and the output minor. -/
theorem infinityTripleParam_residual_system (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    infinityTripleParamInputPair W hΔ j j * X -
        infinityTripleParamInputPair W hΔ j k * (C (1 + A.a₃ * e) * X - C m) =
      (C (infinityTripleLineSeparationSlope W hΔ j k) * X + C f) *
        infinityTripleParamDividedPolynomial W hΔ j k := by
  have h := infinityTripleParamLinePolynomial_sub W hΔ j j k
  rw [infinityTripleParamLinePolynomial_self, infinityTripleParamLinePolynomial_eq,
    infinityTripleParamThirdPolynomial_residual, infinityTripleParamLineZPolynomial_separation] at h
  exact h

/-- The exact constant equation retains the actual input-pair coefficient. -/
theorem infinityTripleParam_residual_coeff_zero (j k : Fin 4) :
    (infinityTripleParamInputPair W hΔ j k).coeff 0 *
        infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) (infinityTripleOutputIndex k) =
      infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k *
        (infinityTripleParamDividedPolynomial W hΔ j k).coeff 0 :=
  infinity_cubic_residual_coeff_zero (infinityTripleParam_residual_system W hΔ j k)

/-- All higher coefficient equations are retained, including tangent constraints at the center. -/
theorem infinityTripleParam_residual_coeff_succ (j k : Fin 4) (i : ℕ) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    let P := infinityTripleParamInputPair W hΔ j j
    let Q := infinityTripleParamInputPair W hΔ j k
    let D := infinityTripleParamDividedPolynomial W hΔ j k
    P.coeff i - (1 + A.a₃ * e) * Q.coeff i + m * Q.coeff (i + 1) =
      infinityTripleLineSeparationSlope W hΔ j k * D.coeff i + f * D.coeff (i + 1) :=
  infinity_cubic_residual_coeff_succ (infinityTripleParam_residual_system W hΔ j k) i

/-- Reciprocity eliminates the opposite residual from the constant coefficient equation. -/
theorem infinityTripleParam_residual_linear_zero (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    let Q := infinityTripleParamInputPair W hΔ j k
    let D := infinityTripleParamDividedPolynomial W hΔ j k
    e * ((1 + A.a₃ * f) * D.coeff 0) +
      m * (Q.coeff 0 + infinityTripleLineSeparationSlope W hΔ j k * D.coeff 0) = 0 := by
  dsimp only
  linear_combination
    (infinityTripleParamDividedPolynomial W hΔ j k).coeff 0 *
      infinityTripleNegLineResidual_reciprocity W hΔ j k +
    infinityTripleParam_residual_coeff_zero W hΔ j k

end FLT.Mazur.WeierstrassIntegralChart
