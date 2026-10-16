/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeEndomorphism

/-!
# Lifting split-node vector fields at every positive smoothing stage

Every derivation of the original split node constructs an endomorphism
of the full xy = e node by perturbing its coordinates with the actual
top parameter power. The original equation is preserved exactly, and
adjacent restriction is the identity on every node function.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)

/-- A selected lift of an arbitrary original split-node function. -/
def topNodeFunctionLift (z : N) : B :=
  Classical.choose (topNodeReduction_surjective R m z)

/-- The selected lift retains the entire original function after reduction. -/
theorem topNodeFunctionLift_reduction (z : N) :
    topNodeReduction R m (topNodeFunctionLift R m z) = z :=
  Classical.choose_spec (topNodeReduction_surjective R m z)

/-- The top-weighted lift is independent of all choices of representatives. -/
theorem topNodeFunctionLift_weighted (z : N) (a : B)
    (ha : topNodeReduction R m a = z) :
    (e) ^ (m + 1) • topNodeFunctionLift R m z = (e) ^ (m + 1) • a := by
  apply sub_eq_zero.mp
  rw [← smul_sub, topNode_parameter_annihilator, (topNodeReduction R m).map_sub,
    topNodeFunctionLift_reduction, ha, sub_self]

local notation "L" => topNodeFunctionLift R m
local notation "t" => algebraMap (S) (B) ((e) ^ (m + 1))

/-- The lifted coordinates satisfy xy = e, including the nilpotent coefficient. -/
theorem topNodeTangentLift_relation (d : Derivation R (N) (N)) :
    (leftCoordinate (e) + (t) * L (d (leftCoordinate (0 : R)))) *
      (rightCoordinate (e) + (t) * L (d (rightCoordinate (0 : R)))) = algebraMap (S) (B) (e) := by
  have ht : (t) ^ 2 = 0 := by
    rw [map_pow]
    exact topNode_parameter_sq R m
  have hr : (e) ^ (m + 1) • (leftCoordinate (e) * L (d (rightCoordinate (0 : R))) +
      rightCoordinate (e) * L (d (leftCoordinate (0 : R)))) = 0 := by
    rw [topNode_parameter_annihilator, (topNodeReduction R m).map_add,
      (topNodeReduction R m).map_mul,
      (topNodeReduction R m).map_mul,
      topNodeReduction_left, topNodeReduction_right,
      topNodeFunctionLift_reduction, topNodeFunctionLift_reduction]
    exact derivation_coordinate_relation (0 : R) d
  have hr' := (Algebra.smul_def ((e) ^ (m + 1)) (leftCoordinate (e) *
    L (d (rightCoordinate (0 : R))) +
    rightCoordinate (e) * L (d (leftCoordinate (0 : R))))).symm.trans hr
  have hxy := coordinate_relation (e)
  linear_combination hxy + hr' + L (d (leftCoordinate (0 : R))) * L (d (rightCoordinate (0
      : R))) * ht

/-- An actual endomorphism of the positive-stage node, constructed from the vector field. -/
def topNodeTangentLift (d : Derivation R (N) (N)) : (B) →ₐ[S] (B) :=
  evaluate (e) (leftCoordinate (e) + (t) * L (d (leftCoordinate (0 : R))))
    (rightCoordinate (e) + (t) * L (d (rightCoordinate (0 : R))))
      (topNodeTangentLift_relation R m d)

/-- The first coordinate of the constructed endomorphism. -/
theorem topNodeTangentLift_left (d : Derivation R (N) (N)) :
    topNodeTangentLift R m d (leftCoordinate (e)) = leftCoordinate (e) + (t) * L (d
      (leftCoordinate (0 : R))) :=
  evaluate_left ..

/-- The second coordinate of the constructed endomorphism. -/
theorem topNodeTangentLift_right (d : Derivation R (N) (N)) :
    topNodeTangentLift R m d (rightCoordinate (e)) = rightCoordinate (e) + (t) * L (d
      (rightCoordinate (0 : R))) :=
  evaluate_right ..

/-- Adjacent restriction kills the actual top power inside the original node ring. -/
theorem topNodeRestriction_parameter_top : topNodeRestriction R m (t) = 0 := by
  rw [topNodeRestriction, ringMap_scalar]
  change algebraMap (Ring R m) (ChartRing (parameter R m))
    (restriction R m ((e) ^ (m + 1))) = 0
  have he : restriction R m ((e) ^ (m + 1)) = 0 :=
    (restriction_eq_zero_iff R m _).mpr ⟨1, mul_one _⟩
  exact (congrArg (algebraMap (Ring R m) (ChartRing (parameter R m))) he).trans (map_zero _)

/-- The constructed lift is the identity on the full preceding-stage node algebra. -/
theorem topNodeTangentLift_restriction (d : Derivation R (N) (N)) (z : B) :
    topNodeRestriction R m (topNodeTangentLift R m d z) = topNodeRestriction R m z := by
  let _ := ((algebraMap (Ring R m) (ChartRing (parameter R m))).comp
    (restriction R m).toRingHom).toAlgebra
  let r : (B) →ₐ[S] ChartRing (parameter R m) :=
    { topNodeRestriction R m with commutes' s := ringMap_scalar .. }
  apply AlgHom.congr_fun (chartRing_hom_ext (e) (r.comp (topNodeTangentLift R m d)) r ?_ ?_) z
  · change topNodeRestriction R m (topNodeTangentLift R m d (leftCoordinate (e))) = _
    rw [topNodeTangentLift_left, (topNodeRestriction R m).map_add,
      (topNodeRestriction R m).map_mul,
      topNodeRestriction_parameter_top, zero_mul, add_zero]
    rfl
  · change topNodeRestriction R m (topNodeTangentLift R m d (rightCoordinate (e))) = _
    rw [topNodeTangentLift_right, (topNodeRestriction R m).map_add,
      (topNodeRestriction R m).map_mul,
      topNodeRestriction_parameter_top, zero_mul, add_zero]
    rfl

end FLT.Mazur.PolygonInfinitesimalStages
