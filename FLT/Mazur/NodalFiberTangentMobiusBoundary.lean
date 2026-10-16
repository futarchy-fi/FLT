/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentMobiusGeometry
public import FLT.Mazur.NodalFiberUnitScalingBoundary
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# Full arithmetic fractional polygon evaluations and boundary parameters

Both polygon coordinates retain their complete arithmetic corrections.
Whenever a boundary coordinate is a unit, the full scheme map factors
through the corresponding Laurent branch with that exact parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (s t : R) (a : Rˣ) (hs : s = (a : R) ^ 2 * t)
local notation "N" => Coordinate t
local notation "L" => TangentOpen s (a : R)
local notation "M" => TangentOpen t (-1 : R)

/-- Pullback of all polygon functions along the full fractional chart. -/
def tangentMobiusEvaluation : PolygonSmoothing.ChartRing t →ₐ[R] L :=
  unitNormalizedEvaluation t t 1 (by simp)
    ((tangentMobiusForward s t a hs).comp (Algebra.algHom R N M))

@[simp] theorem tangentMobiusEvaluation_left :
    tangentMobiusEvaluation s t a hs (PolygonSmoothing.leftCoordinate t) =
      algebraMap R L (↑a⁻¹ : R) * tangentP s (a : R) + algebraMap R L t := by
  rw [tangentMobiusEvaluation, unitNormalizedEvaluation_left]
  simp only [inv_one, Units.val_one, map_one, one_mul]
  exact tangentMobiusForward_p s t a hs

@[simp] theorem tangentMobiusEvaluation_right :
    tangentMobiusEvaluation s t a hs (PolygonSmoothing.rightCoordinate t) =
      tangentFraction s (a : R) := by
  rw [tangentMobiusEvaluation, unitNormalizedEvaluation_right]
  exact tangentMobiusForward_q s t a hs

/-- The coordinate evaluation describes the actual open immersion. -/
theorem tangentMobiusChart_eq_spec :
    tangentMobiusChart s t a hs =
      Spec.map (CommRingCat.ofHom (tangentMobiusEvaluation s t a hs).toRingHom) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

variable {B : Type u} [CommRing B] [Algebra R B]
  (ev : TangentOpen s (a : R) →ₐ[R] B)

/-- The actual translated first parameter factors the full chart through its left boundary. -/
@[reassoc] theorem tangentMobiusChart_left_boundary
    (hu : IsUnit (algebraMap R B (↑a⁻¹ : R) * ev (tangentP s (a : R)) +
      algebraMap R B t)) :
    Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ tangentMobiusChart s t a hs =
      Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := R) hu.unit).toRingHom) ≫
          PolygonSmoothing.leftBranchOpen R t := by
  rw [tangentMobiusChart_eq_spec, ← Spec.map_comp]
  apply PolygonSmoothing.boundary_leftBranchOpen t
    (ev.comp (tangentMobiusEvaluation s t a hs)) hu.unit
  rw [AlgHom.comp_apply, tangentMobiusEvaluation_left, map_add, map_mul,
    AlgHom.commutes, AlgHom.commutes, hu.unit_spec]

/-- The actual fractional second parameter similarly factors the complete right boundary. -/
@[reassoc] theorem tangentMobiusChart_right_boundary
    (hu : IsUnit (ev (tangentFraction s (a : R)))) :
    Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ tangentMobiusChart s t a hs =
      Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := R) hu.unit).toRingHom) ≫
          PolygonSmoothing.rightBranchOpen R t := by
  rw [tangentMobiusChart_eq_spec, ← Spec.map_comp]
  apply PolygonSmoothing.boundary_rightBranchOpen t
    (ev.comp (tangentMobiusEvaluation s t a hs)) hu.unit
  rw [AlgHom.comp_apply, tangentMobiusEvaluation_right, hu.unit_spec]

end FLT.Mazur.NodalFiber
