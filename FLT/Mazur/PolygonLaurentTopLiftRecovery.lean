/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonLaurentTopCoefficient

/-!
# Exact recovery from the double Laurent top layer

Taking the top smoothing coefficient is a left inverse to lifting a reduced
double Laurent polynomial and multiplying by the top parameter power.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
variable (R : Type*) [CommRing R] (m : ℕ)

/-- Extracting the top coefficient recovers every reduced double Laurent polynomial exactly. -/
theorem doubleLaurentStageCoeff_top_lift (p : R[T;T⁻¹][T;T⁻¹]) :
    doubleLaurentStageCoeff R m m
      (C (C (parameter R m)) ^ m *
        coeffMap (coeffMap (algebraMap R (Ring R m))) p) = p := by
  rw [← map_pow, ← map_pow]
  ext a b
  rw [doubleLaurentStageCoeff_coeff, doubleLaurent_constant_mul_coeff,
    coeffMap_coeff, coeffMap_coeff, stageCoeff_top_mul]
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

/-- Equality in the top infinitesimal layer detects equality of the complete reduced polynomial. -/
theorem doubleLaurent_top_lift_injective :
    Function.Injective (fun p : R[T;T⁻¹][T;T⁻¹] ↦
      C (C (parameter R m)) ^ m * coeffMap (coeffMap (algebraMap R (Ring R m))) p) := by
  intro p q he
  have hc := congrArg (doubleLaurentStageCoeff R m m) he
  simpa only [doubleLaurentStageCoeff_top_lift] using hc

end FLT.Mazur.PolygonInfinitesimalStages
