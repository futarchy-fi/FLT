/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleParamCubics

/-!
# Residual coefficients of common centered polynomials

A transformed third factor has leading coefficient 1 + a₃ E and constant term
minus the actual minor. Thus equality with X detects a₃ E, not E; it does not
by itself establish associativity over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Both coefficients of an arbitrary third factor are exact residual expressions. -/
theorem infinityTripleParamThirdPolynomial_residual (j : Fin 4) (i : Fin 7) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    infinityTripleParamThirdPolynomial W hΔ j i =
      C (1 + A.a₃ * infinityTripleNegLineResidual W hΔ i j) * X -
        C (infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) i) := by
  unfold infinityTripleParamThirdPolynomial infinityTripleParamXPolynomial
    infinityTripleParamYPolynomial infinityTripleNegLineResidual infinityTripleNegMinor
    infinityTripleNegY
  simp only [map_add, map_sub, map_neg, map_mul, map_one]
  ring

/-- The constant coefficient is the negative of the oriented point minor. -/
theorem infinityTripleParamThirdPolynomial_coeff_zero (j : Fin 4) (i : Fin 7) :
    (infinityTripleParamThirdPolynomial W hΔ j i).coeff 0 =
      -infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) i := by
  rw [infinityTripleParamThirdPolynomial_residual]
  simp

/-- The leading coefficient retains the line residual multiplied by a₃. -/
theorem infinityTripleParamThirdPolynomial_coeff_one (j : Fin 4) (i : Fin 7) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    (infinityTripleParamThirdPolynomial W hΔ j i).coeff 1 =
      1 + A.a₃ * infinityTripleNegLineResidual W hΔ i j := by
  rw [infinityTripleParamThirdPolynomial_residual]
  simp

/-- Exact equality of third factors detects the minor and the a₃-multiple of the residual. -/
theorem infinityTripleParamThirdPolynomial_eq_X_iff (j : Fin 4) (i : Fin 7) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    infinityTripleParamThirdPolynomial W hΔ j i = X ↔
      A.a₃ * infinityTripleNegLineResidual W hΔ i j = 0 ∧
        infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) i = 0 := by
  dsimp only
  constructor
  · intro h
    have h₀ := congrArg (fun p => p.coeff 0) h
    have h₁ := congrArg (fun p => p.coeff 1) h
    rw [infinityTripleParamThirdPolynomial_coeff_zero, coeff_X_zero] at h₀
    rw [infinityTripleParamThirdPolynomial_coeff_one, coeff_X_one] at h₁
    exact ⟨by linear_combination h₁, neg_eq_zero.mp h₀⟩
  · rintro ⟨hE, hM⟩
    rw [infinityTripleParamThirdPolynomial_residual, hE, hM]
    simp

/-- The constant coefficient of any actual line records its residual at the chosen center. -/
theorem infinityTripleParamLineZPolynomial_coeff_zero (j k : Fin 4) :
    (infinityTripleParamLineZPolynomial W hΔ j k).coeff 0 =
      infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j) -
        infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k := by
  simp only [infinityTripleParamLineZPolynomial, infinityTripleParamXPolynomial,
    infinityTripleParamYPolynomial, coeff_add, coeff_C_zero,
    coeff_neg, mul_coeff_zero, coeff_X_zero, mul_zero, zero_add]
  unfold infinityTripleNegLineResidual
  ring

/-- The centered line's own constant coefficient is the actual output Z coordinate. -/
theorem infinityTripleParamLineZPolynomial_self_coeff_zero (j : Fin 4) :
    (infinityTripleParamLineZPolynomial W hΔ j j).coeff 0 =
      infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j) := by
  rw [infinityTripleParamLineZPolynomial_coeff_zero, infinityTripleNegLineResidual_output,
    sub_zero]

/-- The constant term of the outer line separation is a genuine cross-line residual. -/
theorem infinityTripleParamLineZPolynomial_outer_coeff_zero :
    (infinityTripleParamLineZPolynomial W hΔ 2 2 -
      infinityTripleParamLineZPolynomial W hΔ 2 3).coeff 0 =
      infinityTripleNegLineResidual W hΔ 5 3 := by
  rw [coeff_sub, infinityTripleParamLineZPolynomial_self_coeff_zero,
    infinityTripleParamLineZPolynomial_coeff_zero]
  change infinityTripleScalarZ W hΔ 5 -
    (infinityTripleScalarZ W hΔ 5 - infinityTripleNegLineResidual W hΔ 5 3) = _
  ring

end FLT.Mazur.WeierstrassIntegralChart
