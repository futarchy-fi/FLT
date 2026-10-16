/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageCoefficientChange

/-!
# Faithful scalar extraction at every top smoothing layer

The top parameter power retains arbitrary coefficient scalars, including
nilpotents. Every positive top layer has square zero, so the weighted
Laurent cocycle argument can be applied at successive smoothing orders.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
variable (R : Type*) [CommRing R] (m : ℕ)

/-- The canonical top coefficient recovers the full original scalar at any order. -/
theorem stageCoeff_top_parameter_scalar (r : R) :
    stageCoeff R m m (parameter R m ^ m * algebraMap R (Ring R m) r) = r := by
  simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
    stageCoeff_top_mul R m (algebraMap R (Ring R m) r)

/-- Top-layer scalar cancellation is faithful even over a nonreduced coefficient ring. -/
theorem parameter_top_scalar_injective :
    Function.Injective (fun r : R ↦ parameter R m ^ m * algebraMap R (Ring R m) r) := by
  intro r s he
  have hh := congrArg (stageCoeff R m m) he
  simpa only [stageCoeff_top_parameter_scalar] using hh

/-- The next positive top parameter layer is square-zero on every coefficient algebra. -/
theorem parameter_top_weight_sq (B : Type*) [CommRing B] [Algebra (Ring R (m + 1)) B] :
    (algebraMap (Ring R (m + 1)) B (parameter R (m + 1)) ^ (m + 1)) ^ 2 = 0 := by
  rw [← map_pow, ← map_pow]
  have he : (parameter R (m + 1) ^ (m + 1)) ^ 2 = 0 := by
    rw [← pow_mul]
    apply pow_eq_zero_of_le (show m + 1 + 1 ≤ (m + 1) * 2 by omega)
    exact parameter_pow R (m + 1)
  rw [he, map_zero]

end FLT.Mazur.PolygonInfinitesimalStages
