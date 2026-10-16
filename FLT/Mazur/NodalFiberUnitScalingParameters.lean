/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberUnitScaling

/-!
# Original boundary parameters after full unit normalization

The first parameter acquires the inverse smoothing unit; the second keeps
the entire original function. These formulas apply to arbitrary target
algebras, so nilpotent Laurent corrections are retained.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (c t : R) (u : Rˣ) (hc : c = t * ↑u)
local notation "e" => unitSmoothingEquiv c t u hc

/-- The inverse full normalization divides the first coordinate by the specified unit. -/
@[simp] theorem unitSmoothingEquiv_symm_left :
    (e).symm (PolygonSmoothing.leftCoordinate t) =
      algebraMap R (Coordinate c) (↑u⁻¹ : R) * p c := by
  apply (e).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, AlgEquiv.commutes, unitSmoothingEquiv_p,
    ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- The inverse normalization keeps the second coordinate on the whole node. -/
@[simp] theorem unitSmoothingEquiv_symm_right :
    (e).symm (PolygonSmoothing.rightCoordinate t) = q c := by
  apply (e).injective
  rw [AlgEquiv.apply_symm_apply, unitSmoothingEquiv_q]

variable {B : Type*} [CommRing B] [Algebra R B] (E : Coordinate c →ₐ[R] B)

/-- Transport the original complete boundary evaluation to the normalized polygon chart. -/
def unitNormalizedEvaluation : PolygonSmoothing.ChartRing t →ₐ[R] B :=
  E.comp (e).symm.toAlgHom

/-- The first boundary parameter includes the full inverse-unit correction. -/
@[simp] theorem unitNormalizedEvaluation_left :
    unitNormalizedEvaluation c t u hc E (PolygonSmoothing.leftCoordinate t) =
      algebraMap R B (↑u⁻¹ : R) * E (p c) := by
  simp only [unitNormalizedEvaluation, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    unitSmoothingEquiv_symm_left, map_mul, AlgHom.commutes]

/-- The second boundary parameter retains every original coefficient and Laurent term. -/
@[simp] theorem unitNormalizedEvaluation_right :
    unitNormalizedEvaluation c t u hc E (PolygonSmoothing.rightCoordinate t) = E (q c) := by
  simp only [unitNormalizedEvaluation, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    unitSmoothingEquiv_symm_right]

include hc in
/-- The corrected full parameters have exactly the intended uniform smoothing product. -/
theorem unitNormalizedEvaluation_relation :
    (algebraMap R B (↑u⁻¹ : R) * E (p c)) * E (q c) = algebraMap R B t := by
  rw [← unitNormalizedEvaluation_left c t u hc E,
    ← unitNormalizedEvaluation_right c t u hc E, ← map_mul,
    PolygonSmoothing.coordinate_relation, AlgHom.commutes]

end FLT.Mazur.NodalFiber
