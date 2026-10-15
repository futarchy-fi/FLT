/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeCoordinateDescent
public import FLT.Mazur.PolygonCompleteIdentityFirstActionParameter

/-!
# Exact descent obstructions for the unchanged original coordinate pairs

Both original coordinates have explicit parameter-layer errors relative
to their original node scalings. Their subalgebra membership tests are
therefore equivalent to vanishing of the two concrete Laurent tails.
No vanishing of either tail is asserted here.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
open LaurentPositivePart LaurentBoundaryVectorField PolygonChartScaling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "a" => parameterUnit K
local notation "U" => completeIdentityFirstActionUnit K n h i
local notation "V" => completeIdentityFirstActionReciprocalUnit K n h i
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0
local notation "F" => completeIdentityFirstActionField K n h i

/-- The exact reciprocal original error, including its inverse parameter scaling. -/
def completeIdentityFirstReciprocalError : (R)[T;T⁻¹] :=
  C (reduction (R) 1 (a)⁻¹.val) * reciprocalField (F)

/-- The full reciprocal coordinate has this error over the original smoothing coefficient ring. -/
theorem completeIdentityFirstActionReciprocalUnit_error :
    (V).val = C (a)⁻¹.val * T 1 +
      firstLaurentParameterLift (R) (completeIdentityFirstReciprocalError K n h i) := by
  rw [completeIdentityFirstActionReciprocalUnit_val,
    completeIdentityFirstActionUnit_reciprocal, firstOrderLaurentCoordinate, mul_add]
  change _ + C (a)⁻¹.val * firstLaurentParameterLift (R) (reciprocalField (F)) = _
  rw [firstLaurentParameterLift_scalar]
  rfl

/-- The original left-coordinate difference has zero opposite branch, including nilpotents. -/
theorem completeIdentityFirstActionLeftImage_difference :
    firstNodeBranchLeftImage (R) (U) (V) -
        firstNodeBranchPair (R) (reciprocalScale (e) (a) (leftCoordinate (e))) =
      (firstLaurentParameterLift (R) (O), 0) :=
  firstNodeBranchLeftImage_difference (R) (U) (V) (a) (O)
    (completeIdentityFirstActionUnit_val K n h i)
    (completeIdentityFirstActionReciprocalUnit_reduction K n h i)

/-- Original first-coordinate membership is exactly vanishing of its computed error tail. -/
theorem completeIdentityFirstActionLeftImage_mem_iff :
    firstNodeBranchLeftImage (R) (U) (V) ∈ firstNodeBranchSubalgebra (R) ↔
      boundaryTail (O) = 0 :=
  firstNodeBranchLeftImage_mem_iff (R) (U) (V) (a) (O)
    (completeIdentityFirstActionUnit_val K n h i)
    (completeIdentityFirstActionReciprocalUnit_reduction K n h i)

/-- Original second-coordinate membership is exactly vanishing of its computed reciprocal tail. -/
theorem completeIdentityFirstActionRightImage_mem_iff :
    firstNodeBranchRightImage (R) (U) (V) ∈ firstNodeBranchSubalgebra (R) ↔
      boundaryTail (completeIdentityFirstReciprocalError K n h i) = 0 :=
  firstNodeBranchRightImage_mem_iff (R) (U) (V) (a)
    (completeIdentityFirstReciprocalError K n h i)
    (completeIdentityFirstActionUnit_reduction K n h i)
    (completeIdentityFirstActionReciprocalUnit_error K n h i)

/-- The original whole-branch preservation test is precisely these two actual function tails. -/
theorem completeIdentityFirstActionBranch_preserves_iff_tails :
    (∀ p ∈ firstNodeBranchSubalgebra (R),
      completeIdentityFirstActionBranchEquiv K n h i p ∈ firstNodeBranchSubalgebra (R)) ↔
      boundaryTail (O) = 0 ∧
        boundaryTail (completeIdentityFirstReciprocalError K n h i) = 0 := by
  have he := completeIdentityFirstActionBranchEquiv_toAlgHom K n h i
  change (∀ p ∈ firstNodeBranchSubalgebra (R),
    (completeIdentityFirstActionBranchEquiv K n h i).toAlgHom p ∈
      firstNodeBranchSubalgebra (R)) ↔ _
  rw [he, firstNodeBranchSubstitution_preserves_iff,
    completeIdentityFirstActionLeftImage_mem_iff, completeIdentityFirstActionRightImage_mem_iff]

end FLT.Mazur.PolygonInfinitesimalStages
