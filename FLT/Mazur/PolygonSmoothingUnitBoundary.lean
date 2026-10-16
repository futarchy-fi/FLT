/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Full Laurent factorizations from an invertible boundary coordinate

An arbitrary algebra-valued boundary factors through the standard branch
using its exact unit coordinate. The target algebra may itself be Laurent,
so the parameter can contain nonconstant nilpotent corrections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (t : R) (F : ChartRing t →ₐ[R] B) (w : Bˣ)

/-- An invertible first coordinate determines the full second coordinate. -/
theorem boundary_right_of_left_unit (hw : F (leftCoordinate t) = (w : B)) :
    F (rightCoordinate t) = algebraMap R B t * ↑w⁻¹ := by
  apply (Units.mul_right_inj w).mp
  calc
    ↑w * F (rightCoordinate t) = F (leftCoordinate t) * F (rightCoordinate t) := by rw [hw]
    _ = algebraMap R B t := by rw [← map_mul, coordinate_relation, AlgHom.commutes]
    _ = ↑w * (algebraMap R B t * ↑w⁻¹) := by rw [mul_left_comm, Units.mul_inv, mul_one]

/-- The entire original boundary factors through the left branch with its actual parameter. -/
theorem boundary_leftLaurent (hw : F (leftCoordinate t) = (w : B)) :
    F = (LaurentUnitPoints.evalUnit w).comp (leftLaurentMap t) := by
  apply chartRing_hom_ext t
  · simpa only [AlgHom.comp_apply, leftLaurentMap_left, LaurentUnitPoints.evalUnit_T,
      zpow_one] using hw
  · simpa only [AlgHom.comp_apply, leftLaurentMap_right, map_mul,
      LaurentUnitPoints.evalUnit_C, LaurentUnitPoints.evalUnit_T, zpow_neg_one]
      using boundary_right_of_left_unit t F w hw

/-- The entire opposite boundary factors through the right branch with no parameter loss. -/
theorem boundary_rightLaurent (hw : F (rightCoordinate t) = (w : B)) :
    F = ((LaurentUnitPoints.evalUnit w).comp (leftLaurentMap t)).comp (branchSwapMap t) := by
  have h := boundary_leftLaurent t (F.comp (branchSwapMap t)) w (by
    simpa only [AlgHom.comp_apply, branchSwapMap_left] using hw)
  have he := congrArg (fun g : ChartRing t →ₐ[R] B ↦ g.comp (branchSwapMap t)) h
  simpa only [AlgHom.comp_assoc, branchSwapMap_comp, AlgHom.comp_id] using he

/-- The full scheme boundary is the standard left puncture after its exact parameter map. -/
@[reassoc] theorem boundary_leftBranchOpen (hw : F (leftCoordinate t) = (w : B)) :
    Spec.map (CommRingCat.ofHom F.toRingHom) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) w).toRingHom) ≫
        leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec, ← Spec.map_comp]
  exact congrArg (fun g : ChartRing t →ₐ[R] B ↦ Spec.map (CommRingCat.ofHom g.toRingHom))
    (boundary_leftLaurent t F w hw)

/-- The full scheme boundary similarly uses the original right unit parameter. -/
@[reassoc] theorem boundary_rightBranchOpen (hw : F (rightCoordinate t) = (w : B)) :
    Spec.map (CommRingCat.ofHom F.toRingHom) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) w).toRingHom) ≫
        rightBranchOpen R t := by
  rw [rightBranchOpen_eq_spec, ← Spec.map_comp]
  exact congrArg (fun g : ChartRing t →ₐ[R] B ↦ Spec.map (CommRingCat.ofHom g.toRingHom))
    (boundary_rightLaurent t F w hw)

end FLT.Mazur.PolygonSmoothing
