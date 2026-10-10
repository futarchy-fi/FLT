/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidualElimination
public import FLT.Mazur.WeierstrassInfinityTripleInputPairBezout

/-!
# A quadratic defect detecting the actual output minor

The own-input pair is regular on the full member. Reciprocity therefore
turns vanishing of the cross residual and the quadratic defect into vanishing
of the minor, without cancellation of an evaluated point difference.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The quadratic discrepancy remaining after the expected linear separation correction. -/
def infinityTripleQuadraticDefect (j k : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤)[X] :=
  infinityTripleParamInputPair W hΔ j j - infinityTripleParamInputPair W hΔ j k -
    C (infinityTripleLineSeparationSlope W hΔ j k) *
      infinityTripleParamDividedPolynomial W hΔ j k

/-- There are exactly three possibly nonzero coefficients of the defect. -/
theorem infinityTripleQuadraticDefect_degree (j k : Fin 4) :
    (infinityTripleQuadraticDefect W hΔ j k).natDegree ≤ 2 := by
  have hp := infinityTripleParamInputPair_degree W hΔ j j
  have hq := infinityTripleParamInputPair_degree W hΔ j k
  have hd := infinityTripleParamDividedPolynomial_degree W hΔ j k
  unfold infinityTripleQuadraticDefect
  compute_degree!

/-- The actual primitive own-input pair is the minor's coefficient in the elimination syzygy. -/
theorem infinityTripleQuadraticDefect_syzygy (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    C m * infinityTripleParamInputPair W hΔ j j +
        infinityTripleQuadraticDefect W hΔ j k * (X - C m) =
      C e * (C A.a₃ * infinityTripleParamInputPair W hΔ j k * X -
        C (1 + A.a₃ * f) * infinityTripleParamDividedPolynomial W hΔ j k) :=
  infinity_residual_elimination _ _ _ _ _ _ _ _
    (infinityTripleParam_residual_system W hΔ j k)
    (infinityTripleNegLineResidual_reciprocity W hΔ j k)

/-- Zero residual and zero defect force the actual minor to vanish on the entire member. -/
theorem infinityTripleQuadraticDefect_minor_eq_zero (j k : Fin 4)
    (he : infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j = 0)
    (hd : infinityTripleQuadraticDefect W hΔ j k = 0) :
    infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k) = 0 := by
  have hc := infinityTripleParam_residual_system W hΔ j k
  have hr := infinityTripleNegLineResidual_reciprocity W hΔ j k
  dsimp only at hc hr
  rw [he] at hc hr
  exact infinity_residual_minor_eq_zero _ _ _ _ _ _ _
    (infinityTripleParamInputPair_regular W hΔ j j) hc hr hd

/-- Conversely both zero residuals and minor force the entire quadratic discrepancy to vanish. -/
theorem infinityTripleQuadraticDefect_eq_zero (j k : Fin 4)
    (he : infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j = 0)
    (hm : infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k) = 0) :
    infinityTripleQuadraticDefect W hΔ j k = 0 := by
  have h := infinityTripleQuadraticDefect_syzygy W hΔ j k
  dsimp only at h
  rw [he, hm, map_zero, zero_mul, zero_add, sub_zero] at h
  ext i
  have hc := congrArg (fun p => p.coeff (i + 1)) h
  simpa only [coeff_mul_X, coeff_zero, zero_mul] using hc

/-- The scalar minor can be replaced exactly by the full quadratic defect. -/
theorem infinityTripleQuadraticDefect_criterion (j k : Fin 4) :
    (infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j = 0 ∧
      infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
        (infinityTripleOutputIndex k) = 0) ↔
    (infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j = 0 ∧
      infinityTripleQuadraticDefect W hΔ j k = 0) := by
  constructor
  · rintro ⟨he, hm⟩
    exact ⟨he, infinityTripleQuadraticDefect_eq_zero W hΔ j k he hm⟩
  · rintro ⟨he, hd⟩
    exact ⟨he, infinityTripleQuadraticDefect_minor_eq_zero W hΔ j k he hd⟩

end FLT.Mazur.WeierstrassIntegralChart
