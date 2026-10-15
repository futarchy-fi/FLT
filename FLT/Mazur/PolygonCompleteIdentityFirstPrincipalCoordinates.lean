/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPrincipalObstruction
public import FLT.Mazur.PolygonCompleteIdentityFirstCoordinateDescent

/-!
# Exact principal-part coordinates of the original node obstruction

Compute the canonical coefficient and remainder on both original node
coordinates. The reciprocal coordinate retains the shared-constant correction,
which distinguishes its actual quotient representative from its raw tail.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter PolygonScalingNaturality
open LaurentNodePrincipalParts LaurentPositivePart PolygonChartScaling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField

/-- The second coordinate error has zero left branch, including its entire nilpotent layer. -/
theorem firstNodeBranchRightImage_difference (R : Type) [CommRing R]
    (u v : (Ring R 1)[T;T⁻¹]ˣ) (a : (Ring R 1)ˣ) (q : R[T;T⁻¹])
    (hu : coeffMap (reduction R 1).toRingHom u.val = C (reduction R 1 a.val) * T 1)
    (hv : v.val = C a⁻¹.val * T 1 + firstLaurentParameterLift R q) :
    firstNodeBranchRightImage R u v -
        firstNodeBranchPair R (reciprocalScale (parameter R 1) a
          (rightCoordinate (parameter R 1))) =
      (0, firstLaurentParameterLift R q) := by
  rw [← firstNodeBranchPair_scaling, firstNodeBranchSubstitution_right]
  apply Prod.ext
  · change C (parameter R 1) * u⁻¹.val -
        C (parameter R 1) * (coordinateUnit a)⁻¹.val = 0
    rw [firstLaurent_parameter_inverse_scaling R u a hu, sub_self]
  · change v.val - (coordinateUnit a⁻¹).val = firstLaurentParameterLift R q
    rw [hv]
    change C a⁻¹.val * T 1 + firstLaurentParameterLift R q - C a⁻¹.val * T 1 = _
    abel

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) 1
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0
local notation "Q" => completeIdentityFirstReciprocalError K n h i

/-- The full reduced defect on the left generator is the original weighted error. -/
theorem completeIdentityFirstReducedDefect_left :
    completeIdentityFirstReducedDefect K n h i (leftCoordinate (0 : R)) =
      firstNodeParameterPair (R) ((O), 0) := by
  rw [← firstNodeReduction_left (R), completeIdentityFirstReducedDefect_reduction,
    completeIdentityFirstActionNodeDefect_apply]
  change (completeIdentityFirstActionBranchEquiv K n h i).toAlgHom
    (firstNodeBranchPair (R) (leftCoordinate (e))) - _ = _
  rw [completeIdentityFirstActionBranchEquiv_toAlgHom, firstNodeBranchSubstitution_left,
    completeIdentityFirstActionLeftImage_difference]
  change (_, 0) = (_, firstLaurentParameterLift (R) 0)
  rw [firstLaurentParameterLift_zero]

/-- The full reduced defect on the right generator is the original weighted reciprocal error. -/
theorem completeIdentityFirstReducedDefect_right :
    completeIdentityFirstReducedDefect K n h i (rightCoordinate (0 : R)) =
      firstNodeParameterPair (R) (0, (Q)) := by
  rw [← firstNodeReduction_right (R), completeIdentityFirstReducedDefect_reduction,
    completeIdentityFirstActionNodeDefect_apply]
  change (completeIdentityFirstActionBranchEquiv K n h i).toAlgHom
    (firstNodeBranchPair (R) (rightCoordinate (e))) - _ = _
  rw [completeIdentityFirstActionBranchEquiv_toAlgHom, firstNodeBranchSubstitution_right,
    firstNodeBranchRightImage_difference (R) _ _ (parameterUnit K) (Q)
      (completeIdentityFirstActionUnit_reduction K n h i)
      (completeIdentityFirstActionReciprocalUnit_error K n h i)]
  change (0, _) = (firstLaurentParameterLift (R) 0, _)
  rw [firstLaurentParameterLift_zero]

/-- Coefficient extraction retains exactly the two original left-generator coefficients. -/
theorem completeIdentityFirstDefectCoefficient_left :
    completeIdentityFirstDefectCoefficient K n h i (leftCoordinate (0 : R)) = ((O), 0) := by
  change firstNodePairCoefficient (R)
    (completeIdentityFirstReducedDefect K n h i (leftCoordinate (0 : R))) = _
  rw [completeIdentityFirstReducedDefect_left, firstNodePairCoefficient_weighted]

/-- The right-generator coefficients retain the reciprocal original action with no substitution. -/
theorem completeIdentityFirstDefectCoefficient_right :
    completeIdentityFirstDefectCoefficient K n h i (rightCoordinate (0 : R)) = (0, (Q)) := by
  change firstNodePairCoefficient (R)
    (completeIdentityFirstReducedDefect K n h i (rightCoordinate (0 : R))) = _
  rw [completeIdentityFirstReducedDefect_right, firstNodePairCoefficient_weighted]

/-- The first original obstruction is represented by its left nonpositive tail. -/
theorem completeIdentityFirstPrincipalObstruction_left :
    completeIdentityFirstPrincipalObstruction K n h i (leftCoordinate (0 : R)) =
      (boundaryTail (O), 0) := by
  change principalParts (completeIdentityFirstDefectCoefficient K n h i _) = _
  rw [completeIdentityFirstDefectCoefficient_left, principalParts_apply]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero, sub_zero,
    ← tailLinear_apply]

/-- The reciprocal original obstruction includes the exact shared-constant mismatch. -/
theorem completeIdentityFirstPrincipalObstruction_right :
    completeIdentityFirstPrincipalObstruction K n h i (rightCoordinate (0 : R)) =
      (-C ((Q).coeff 0), boundaryTail (Q) - C ((Q).coeff 0)) := by
  change principalParts (completeIdentityFirstDefectCoefficient K n h i _) = _
  rw [completeIdentityFirstDefectCoefficient_right, principalParts_apply]
  simp only [← tailLinear_apply, map_zero, zero_sub]

end FLT.Mazur.PolygonInfinitesimalStages
