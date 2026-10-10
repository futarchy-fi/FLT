/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleInputPairCoefficients

/-!
# A unit certificate for the three actual input-pair coefficients

Although no individual coefficient need be invertible, an explicit combination
of all three is the genuine unit scale. This licenses simultaneous scalar
cancellation without an additional open condition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Every transformed input shares the same explicit Bezout coefficients. -/
theorem infinityTripleParamInput_bezout (j : Fin 4) (i : Fin 7) :
    infinityTripleNegY W hΔ (infinityTripleOutputIndex j) *
        infinityTripleParamInputSlope W hΔ j i -
      infinityTripleParamDirectionY W hΔ j * infinityTripleParamInputConstant W hΔ j i =
        1 := by
  have h := infinityTripleParam_determinant W hΔ j
  change infinityTripleParamDirectionX W hΔ j *
    infinityTripleNegY W hΔ (infinityTripleOutputIndex j) -
    infinityTripleScalarX W hΔ (infinityTripleOutputIndex j) *
      infinityTripleParamDirectionY W hΔ j = 1 at h
  unfold infinityTripleParamInputSlope infinityTripleParamInputConstant
  linear_combination h

/-- The three quadratic coefficients have an explicit linear combination equal to the scale. -/
theorem infinityTripleParamInputPair_bezout (j k : Fin 4) :
    let n := infinityTripleNegY W hΔ (infinityTripleOutputIndex j)
    let v := infinityTripleParamDirectionY W hΔ j
    let Q := infinityTripleParamInputPair W hΔ j k
    v ^ 2 * Q.coeff 0 - n * v * Q.coeff 1 + n ^ 2 * Q.coeff 2 =
      infinityTripleScalarScale W hΔ k := by
  dsimp only
  rw [infinityTripleParamInputPair_coeff_zero, infinityTripleParamInputPair_coeff_one,
    infinityTripleParamInputPair_coeff_two]
  have hl := infinityTripleParamInput_bezout W hΔ j (infinityTripleLeftIndex k)
  have hr := infinityTripleParamInput_bezout W hΔ j (infinityTripleRightIndex k)
  linear_combination infinityTripleScalarScale W hΔ k *
    (infinityTripleNegY W hΔ (infinityTripleOutputIndex j) *
        infinityTripleParamInputSlope W hΔ j (infinityTripleRightIndex k) -
      infinityTripleParamDirectionY W hΔ j *
        infinityTripleParamInputConstant W hΔ j (infinityTripleRightIndex k)) * hl +
    infinityTripleScalarScale W hΔ k * hr

/-- The explicit coefficient combination is a unit on the entire true triple member. -/
theorem infinityTripleParamInputPair_bezout_unit (j k : Fin 4) :
    let n := infinityTripleNegY W hΔ (infinityTripleOutputIndex j)
    let v := infinityTripleParamDirectionY W hΔ j
    let Q := infinityTripleParamInputPair W hΔ j k
    IsUnit (v ^ 2 * Q.coeff 0 - n * v * Q.coeff 1 + n ^ 2 * Q.coeff 2) := by
  dsimp only
  rw [infinityTripleParamInputPair_bezout]
  exact infinityTripleScalar_scale_unit W hΔ k

/-- An element annihilating all three coefficients is zero, even if each is a zero divisor. -/
theorem infinityTripleParamInputPair_annihilator (j k : Fin 4)
    (t : Γ(InfinityTripleFull W hΔ, ⊤))
    (h₀ : t * (infinityTripleParamInputPair W hΔ j k).coeff 0 = 0)
    (h₁ : t * (infinityTripleParamInputPair W hΔ j k).coeff 1 = 0)
    (h₂ : t * (infinityTripleParamInputPair W hΔ j k).coeff 2 = 0) : t = 0 := by
  apply (infinityTripleScalar_scale_unit W hΔ k).mul_right_inj.mp
  have h := infinityTripleParamInputPair_bezout W hΔ j k
  dsimp only at h
  linear_combination
    (infinityTripleParamDirectionY W hΔ j) ^ 2 * h₀ -
    infinityTripleNegY W hΔ (infinityTripleOutputIndex j) *
      infinityTripleParamDirectionY W hΔ j * h₁ +
    (infinityTripleNegY W hΔ (infinityTripleOutputIndex j)) ^ 2 * h₂ - t * h

/-- Equality can be checked after multiplication by these three scalar coefficients. -/
theorem infinityTripleParamInputPair_scalar_ext (j k : Fin 4)
    (s t : Γ(InfinityTripleFull W hΔ, ⊤))
    (h₀ : s * (infinityTripleParamInputPair W hΔ j k).coeff 0 =
      t * (infinityTripleParamInputPair W hΔ j k).coeff 0)
    (h₁ : s * (infinityTripleParamInputPair W hΔ j k).coeff 1 =
      t * (infinityTripleParamInputPair W hΔ j k).coeff 1)
    (h₂ : s * (infinityTripleParamInputPair W hΔ j k).coeff 2 =
      t * (infinityTripleParamInputPair W hΔ j k).coeff 2) : s = t := by
  apply sub_eq_zero.mp
  apply infinityTripleParamInputPair_annihilator W hΔ j k (s - t)
  · linear_combination h₀
  · linear_combination h₁
  · linear_combination h₂

end FLT.Mazur.WeierstrassIntegralChart
