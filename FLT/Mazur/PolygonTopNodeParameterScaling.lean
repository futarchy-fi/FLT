/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentTopParameterSubstitution
public import FLT.Mazur.PolygonStageNodeBranchSubstitution
public import FLT.Mazur.PolygonSmoothingReciprocalScaling
public import FLT.Mazur.PolygonChartScaling

/-!
# Unconditional descent on the whole parameter ideal

Two branch substitutions restricting to reciprocal scaling preserve every
parameter-weighted node function. On this entire ideal their action is
exactly the original node scaling, with no coordinate-membership assumption.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentUnitPoints PolygonChartScaling
open PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]

variable (u v : (Ring R (m + 1))[T;T⁻¹]ˣ) (a : (Ring R (m + 1))ˣ)
  (hu : coeffMap (restriction R m).toRingHom u.val = C (restriction R m a.val) * T 1)
  (hv : coeffMap (restriction R m).toRingHom v.val = C (restriction R m a⁻¹.val) * T 1)

include hu hv in
/-- Every node function multiplied by the parameter has its exact original scaling image. -/
theorem topNodeBranchSubstitution_parameter_scaling (z : B) :
    stageNodeBranchSubstitution R (m + 1) u v (stageNodeBranchPair R (m + 1) ((e) • z)) =
      stageNodeBranchPair R (m + 1) (reciprocalScale (e) a ((e) • z)) := by
  rw [← stageNodeBranchPair_scaling]
  rw [Algebra.smul_def (e) z]
  apply Prod.ext
  · change evalUnit u (leftLaurentMap (e) (algebraMap (S) (B) (e) * z)) =
      evalUnit (coordinateUnit a) (leftLaurentMap (e) (algebraMap (S) (B) (e) * z))
    rw [map_mul, AlgHom.commutes, ← C_eq_algebraMap]
    apply topLaurent_evalUnit_weighted_eq R m
    apply hu.trans
    change _ = coeffMap (restriction R m).toRingHom (C a.val * T 1)
    rw [map_mul, coeffMap_C, coeffMap_T]
    rfl
  · change evalUnit v
        (leftLaurentMap (e) (branchSwapMap (e) (algebraMap (S) (B) (e) * z))) =
      evalUnit (coordinateUnit a⁻¹)
        (leftLaurentMap (e) (branchSwapMap (e) (algebraMap (S) (B) (e) * z)))
    rw [map_mul, AlgHom.commutes, map_mul, AlgHom.commutes, ← C_eq_algebraMap]
    apply topLaurent_evalUnit_weighted_eq R m
    apply hv.trans
    change _ = coeffMap (restriction R m).toRingHom (C a⁻¹.val * T 1)
    rw [map_mul, coeffMap_C, coeffMap_T]
    rfl

include hu hv in
/-- Thus the actual parameter ideal descends with no hypothesis about either coordinate. -/
theorem topNodeBranchSubstitution_parameter_mem (z : B) :
    stageNodeBranchSubstitution R (m + 1) u v (stageNodeBranchPair R (m + 1) ((e) • z)) ∈
      stageNodeBranchSubalgebra R (m + 1) := by
  rw [topNodeBranchSubstitution_parameter_scaling R m u v a hu hv]
  exact ⟨_, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
