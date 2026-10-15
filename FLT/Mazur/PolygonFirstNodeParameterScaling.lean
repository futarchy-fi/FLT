/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentFirstParameterSubstitution
public import FLT.Mazur.PolygonFirstNodeSubalgebraPreservation
public import FLT.Mazur.PolygonSmoothingReciprocalScaling
public import FLT.Mazur.PolygonChartScaling

/-!
# Unconditional descent on the whole parameter ideal

Two branch substitutions reducing to reciprocal scaling preserve every
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
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]

/-- Full reciprocal node scaling has exactly the two prescribed Laurent scaling restrictions. -/
theorem firstNodeBranchPair_scaling (a : (S)ˣ) (z : B) :
    firstNodeBranchSubstitution R (coordinateUnit a) (coordinateUnit a⁻¹)
        (firstNodeBranchPair R z) =
      firstNodeBranchPair R (reciprocalScale (e) a z) := by
  have he : (firstNodeBranchSubstitution R (coordinateUnit a) (coordinateUnit a⁻¹)).comp
      (firstNodeBranchPair R) = (firstNodeBranchPair R).comp (reciprocalScale (e) a) := by
    apply chartRing_hom_ext (e)
    · change firstNodeBranchSubstitution R _ _ (firstNodeBranchPair R (leftCoordinate (e))) = _
      rw [firstNodeBranchSubstitution_left]
      apply Prod.ext
      · simp only [firstNodeBranchLeftImage, firstNodeBranchPair, AlgHom.comp_apply,
          AlgHom.prod_apply, reciprocalScale_left, map_mul, AlgHom.commutes,
          leftLaurentMap_left, coordinateUnit]
        rfl
      · change C (e) * (coordinateUnit a⁻¹)⁻¹.val =
          leftLaurentMap (e) (branchSwapMap (e) (reciprocalScale (e) a (leftCoordinate (e))))
        simp only [reciprocalScale_left, map_mul, AlgHom.commutes, branchSwapMap_left,
          leftLaurentMap_right, ← C_eq_algebraMap]
        change C (e) * (C (a⁻¹)⁻¹.val * T (-1)) = C a.val * (C (e) * T (-1))
        rw [inv_inv]
        ring
    · change firstNodeBranchSubstitution R _ _ (firstNodeBranchPair R (rightCoordinate (e))) = _
      rw [firstNodeBranchSubstitution_right]
      apply Prod.ext
      · change C (e) * (coordinateUnit a)⁻¹.val =
          leftLaurentMap (e) (reciprocalScale (e) a (rightCoordinate (e)))
        simp only [reciprocalScale_right, map_mul, AlgHom.commutes,
          leftLaurentMap_right, ← C_eq_algebraMap]
        change C (e) * (C a⁻¹.val * T (-1)) = C a⁻¹.val * (C (e) * T (-1))
        ring
      · change (coordinateUnit a⁻¹).val =
          leftLaurentMap (e) (branchSwapMap (e) (reciprocalScale (e) a (rightCoordinate (e))))
        rw [reciprocalScale_right, map_mul, AlgHom.commutes, branchSwapMap_right,
          map_mul, AlgHom.commutes, leftLaurentMap_left]
        rfl
  exact AlgHom.congr_fun he z

variable (u v : (Ring R 1)[T;T⁻¹]ˣ) (a : (Ring R 1)ˣ)
  (hu : coeffMap (reduction R 1).toRingHom u.val = C (reduction R 1 a.val) * T 1)
  (hv : coeffMap (reduction R 1).toRingHom v.val = C (reduction R 1 a⁻¹.val) * T 1)

include hu hv in
/-- Every node function multiplied by the parameter has its exact original scaling image. -/
theorem firstNodeBranchSubstitution_parameter_scaling (z : B) :
    firstNodeBranchSubstitution R u v (firstNodeBranchPair R ((e) • z)) =
      firstNodeBranchPair R (reciprocalScale (e) a ((e) • z)) := by
  rw [← firstNodeBranchPair_scaling]
  rw [Algebra.smul_def (e) z]
  apply Prod.ext
  · change evalUnit u (leftLaurentMap (e) (algebraMap (S) (B) (e) * z)) =
      evalUnit (coordinateUnit a) (leftLaurentMap (e) (algebraMap (S) (B) (e) * z))
    rw [map_mul, AlgHom.commutes, ← C_eq_algebraMap]
    apply firstLaurent_evalUnit_weighted_eq R
    apply hu.trans
    change _ = coeffMap (reduction R 1).toRingHom (C a.val * T 1)
    rw [map_mul, coeffMap_C, coeffMap_T]
    rfl
  · change evalUnit v
        (leftLaurentMap (e) (branchSwapMap (e) (algebraMap (S) (B) (e) * z))) =
      evalUnit (coordinateUnit a⁻¹)
        (leftLaurentMap (e) (branchSwapMap (e) (algebraMap (S) (B) (e) * z)))
    rw [map_mul, AlgHom.commutes, map_mul, AlgHom.commutes, ← C_eq_algebraMap]
    apply firstLaurent_evalUnit_weighted_eq R
    apply hv.trans
    change _ = coeffMap (reduction R 1).toRingHom (C a⁻¹.val * T 1)
    rw [map_mul, coeffMap_C, coeffMap_T]
    rfl

include hu hv in
/-- Thus the actual parameter ideal descends with no hypothesis about either coordinate. -/
theorem firstNodeBranchSubstitution_parameter_mem (z : B) :
    firstNodeBranchSubstitution R u v (firstNodeBranchPair R ((e) • z)) ∈
      firstNodeBranchSubalgebra R := by
  rw [firstNodeBranchSubstitution_parameter_scaling R u v a hu hv]
  exact ⟨_, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
