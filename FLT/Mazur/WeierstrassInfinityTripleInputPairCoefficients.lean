/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleResidualDegree

/-!
# Explicit coefficients of the actual input-pair quadratics

The coefficients retain the genuine output normalizer and both transformed
input factors. No leading or constant coefficient is declared invertible.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The X direction of the determinant-one parameter change. -/
def infinityTripleParamDirectionX (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  -(1 + (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))).a₃ *
    infinityTripleLineIntercept W hΔ j)

/-- The Y direction of the same parameter change. -/
def infinityTripleParamDirectionY (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  A.a₁ + A.a₃ * infinityTripleScalarSlope W hΔ j

/-- The linear coefficient of a transformed actual input factor. -/
def infinityTripleParamInputSlope (j : Fin 4) (i : Fin 7) :
    Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleParamDirectionX W hΔ j -
    infinityTripleScalarX W hΔ i * infinityTripleParamDirectionY W hΔ j

/-- The constant coefficient of a transformed actual input factor. -/
def infinityTripleParamInputConstant (j : Fin 4) (i : Fin 7) :
    Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarX W hΔ (infinityTripleOutputIndex j) -
    infinityTripleScalarX W hΔ i *
      infinityTripleNegY W hΔ (infinityTripleOutputIndex j)

/-- The actual first coordinate in scalar coefficient form. -/
theorem infinityTripleParamXPolynomial_linear (j : Fin 4) :
    infinityTripleParamXPolynomial W hΔ j =
      C (infinityTripleParamDirectionX W hΔ j) * X +
        C (infinityTripleScalarX W hΔ (infinityTripleOutputIndex j)) := by
  simp only [infinityTripleParamXPolynomial, infinityTripleParamDirectionX, map_neg]

/-- The actual second coordinate in scalar coefficient form. -/
theorem infinityTripleParamYPolynomial_linear (j : Fin 4) :
    infinityTripleParamYPolynomial W hΔ j =
      C (infinityTripleParamDirectionY W hΔ j) * X +
        C (infinityTripleNegY W hΔ (infinityTripleOutputIndex j)) := rfl

/-- The two scalar expressions really are the coefficients of the actual input. -/
theorem infinityTripleParamInputPolynomial_linear (j : Fin 4) (i : Fin 7) :
    infinityTripleParamInputPolynomial W hΔ j i =
      C (infinityTripleParamInputSlope W hΔ j i) * X +
        C (infinityTripleParamInputConstant W hΔ j i) := by
  simp only [infinityTripleParamInputPolynomial, infinityTripleParamXPolynomial_linear,
    infinityTripleParamYPolynomial_linear, infinityTripleParamInputSlope,
    infinityTripleParamInputConstant, map_sub, map_mul]
  ring

/-- Full expansion of the genuine scaled input pair. -/
theorem infinityTripleParamInputPair_expand (j k : Fin 4) :
    let s := infinityTripleScalarScale W hΔ k
    let a := infinityTripleParamInputSlope W hΔ j (infinityTripleLeftIndex k)
    let b := infinityTripleParamInputSlope W hΔ j (infinityTripleRightIndex k)
    let c := infinityTripleParamInputConstant W hΔ j (infinityTripleLeftIndex k)
    let d := infinityTripleParamInputConstant W hΔ j (infinityTripleRightIndex k)
    infinityTripleParamInputPair W hΔ j k =
      C (s * a * b) * X ^ 2 + C (s * (a * d + c * b)) * X + C (s * c * d) := by
  simp only [infinityTripleParamInputPair, infinityTripleParamInputPolynomial_linear,
    map_mul, map_add]
  ring

/-- The constant coefficient involves the actual two point differences. -/
theorem infinityTripleParamInputPair_coeff_zero (j k : Fin 4) :
    (infinityTripleParamInputPair W hΔ j k).coeff 0 =
      infinityTripleScalarScale W hΔ k *
        infinityTripleParamInputConstant W hΔ j (infinityTripleLeftIndex k) *
        infinityTripleParamInputConstant W hΔ j (infinityTripleRightIndex k) := by
  rw [infinityTripleParamInputPair_expand]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- The linear coefficient keeps both cross terms. -/
theorem infinityTripleParamInputPair_coeff_one (j k : Fin 4) :
    (infinityTripleParamInputPair W hΔ j k).coeff 1 =
      infinityTripleScalarScale W hΔ k *
        (infinityTripleParamInputSlope W hΔ j (infinityTripleLeftIndex k) *
          infinityTripleParamInputConstant W hΔ j (infinityTripleRightIndex k) +
        infinityTripleParamInputConstant W hΔ j (infinityTripleLeftIndex k) *
          infinityTripleParamInputSlope W hΔ j (infinityTripleRightIndex k)) := by
  rw [infinityTripleParamInputPair_expand]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- The quadratic coefficient is the scaled product of the two actual directions. -/
theorem infinityTripleParamInputPair_coeff_two (j k : Fin 4) :
    (infinityTripleParamInputPair W hΔ j k).coeff 2 =
      infinityTripleScalarScale W hΔ k *
        infinityTripleParamInputSlope W hΔ j (infinityTripleLeftIndex k) *
        infinityTripleParamInputSlope W hΔ j (infinityTripleRightIndex k) := by
  rw [infinityTripleParamInputPair_expand]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

end FLT.Mazur.WeierstrassIntegralChart
