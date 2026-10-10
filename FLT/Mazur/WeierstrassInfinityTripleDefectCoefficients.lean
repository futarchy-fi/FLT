/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleQuadraticDefect
public import FLT.Mazur.WeierstrassInfinityQuadraticWeight

/-!
# Explicit scalar certificates for the quadratic defect

Every defect coefficient is an explicit linear combination of the two original
residuals. In the other direction, a weighted combination recovers the minor
multiplied by the genuine unit scale. No individual coefficient is canceled.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The polynomial multiplying the first residual after elimination of the opposite residual. -/
def infinityTripleResidualMultiplier (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
  let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
  C A.a₃ * infinityTripleParamInputPair W hΔ j k * X -
    C (1 + A.a₃ * f) * infinityTripleParamDividedPolynomial W hΔ j k

/-- Each coefficient is an explicit linear combination of the actual residual and minor. -/
theorem infinityTripleQuadraticDefect_coeff (j k : Fin 4) (i : ℕ) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    let r := infinityTripleLineSeparationSlope W hΔ j k
    let Q := infinityTripleParamInputPair W hΔ j k
    let D := infinityTripleParamDividedPolynomial W hΔ j k
    (infinityTripleQuadraticDefect W hΔ j k).coeff i =
      e * (A.a₃ * Q.coeff i - (1 + A.a₃ * f) * D.coeff (i + 1)) -
        m * (Q.coeff (i + 1) + r * D.coeff (i + 1)) := by
  have hc := infinityTripleParam_residual_coeff_succ W hΔ j k i
  have hr := infinityTripleNegLineResidual_reciprocity W hΔ j k
  dsimp only at hc hr ⊢
  simp only [infinityTripleQuadraticDefect, coeff_sub, coeff_C_mul]
  linear_combination hc +
    (infinityTripleParamDividedPolynomial W hΔ j k).coeff (i + 1) * hr

/-- The three defect coefficients recover the minor up to the actual invertible scale. -/
theorem infinityTripleQuadraticDefect_minor_certificate (j k : Fin 4) :
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    let n := infinityTripleNegY W hΔ (infinityTripleOutputIndex j)
    let v := infinityTripleParamDirectionY W hΔ j
    let H := infinityTripleQuadraticDefect W hΔ j k
    m * infinityTripleScalarScale W hΔ j =
      e * infinityQuadraticWeight n v (infinityTripleResidualMultiplier W hΔ j k) +
        n * v * H.coeff 0 - n ^ 2 * H.coeff 1 + m * infinityQuadraticWeight n v H := by
  have h := infinityQuadraticWeight_syzygy
    (infinityTripleNegY W hΔ (infinityTripleOutputIndex j))
    (infinityTripleParamDirectionY W hΔ j) _ _ _ _ _
    (infinityTripleQuadraticDefect_syzygy W hΔ j k)
  dsimp only [infinityQuadraticWeight] at h
  rw [infinityTripleParamInputPair_bezout] at h
  exact h

/-- Vanishing of the defect is a finite check of exactly its first three coefficients. -/
theorem infinityTripleQuadraticDefect_eq_zero_iff_coeff (j k : Fin 4) :
    infinityTripleQuadraticDefect W hΔ j k = 0 ↔
      ∀ i : Fin 3, (infinityTripleQuadraticDefect W hΔ j k).coeff i = 0 := by
  constructor
  · intro h i
    rw [h, coeff_zero]
  · intro h
    ext i
    by_cases hi : i < 3
    · exact h ⟨i, hi⟩
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (infinityTripleQuadraticDefect_degree W hΔ j k) (by omega))

end FLT.Mazur.WeierstrassIntegralChart
