/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeBranchAutomorphism
public import FLT.Mazur.PolygonCompleteIdentityFirstActionBoundary

/-!
# Original action extensions from preservation of two node coordinates

Retain the unchanged universal action unit and its reciprocal as the two
branch coordinates. Membership of their two explicit coordinate pairs in
the original node subalgebra constructs the missing node maps, rather than
assuming maps extending the action. This membership remains to be proved
from the original cubic geometry; no support vanishing is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality
open LaurentCoefficientEvaluation LaurentFirstStageParameter PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "a" => parameterUnit K
local notation "U" => completeIdentityFirstActionUnit K n h i

/-- The actual original action viewed in its reciprocal input and output coordinates. -/
def completeIdentityFirstActionReciprocalUnit : (S)[T;T⁻¹]ˣ :=
  Units.map invert.toMonoidHom (U)⁻¹
local notation "V" => completeIdentityFirstActionReciprocalUnit K n h i

/-- The reciprocal unit retains exactly the original reciprocal action coordinate. -/
theorem completeIdentityFirstActionReciprocalUnit_val : (V).val = invert (U)⁻¹.val := rfl

/-- The original full action has precisely its original scaling as closed reduction. -/
theorem completeIdentityFirstActionUnit_reduction :
    coeffMap (reduction (R) 1).toRingHom (U).val =
      C (reduction (R) 1 (a).val) * T 1 := by
  have he : (reduction (R) 1).toRingHom (e) = 0 := reduction_parameter (R) 1
  rw [completeIdentityFirstActionUnit_val]
  simp only [map_add, map_mul, coeffMap_C, coeffMap_T, he, map_zero, zero_mul, add_zero]
  rfl

/-- The reciprocal original action has inverse scaling as its complete closed reduction. -/
theorem completeIdentityFirstActionReciprocalUnit_reduction :
    coeffMap (reduction (R) 1).toRingHom (V).val =
      C (reduction (R) 1 (a)⁻¹.val) * T 1 := by
  have he : (reduction (R) 1).toRingHom (e) = 0 := reduction_parameter (R) 1
  rw [completeIdentityFirstActionReciprocalUnit_val,
    completeIdentityFirstActionUnit_reciprocal, firstOrderLaurentCoordinate]
  simp only [map_add, map_mul, coeffMap_C, coeffMap_T, he, map_zero, zero_mul, add_zero]
  rfl

variable
  (hx : firstNodeBranchLeftImage K[T;T⁻¹] (completeIdentityFirstActionUnit K n h i)
    (completeIdentityFirstActionReciprocalUnit K n h i) ∈ firstNodeBranchSubalgebra K[T;T⁻¹])
  (hy : firstNodeBranchRightImage K[T;T⁻¹] (completeIdentityFirstActionUnit K n h i)
    (completeIdentityFirstActionReciprocalUnit K n h i) ∈ firstNodeBranchSubalgebra K[T;T⁻¹])

/-- Original coordinate-subalgebra preservation constructs the entire node automorphism. -/
def completeIdentityFirstActionSubalgebraNode : ChartRing (e) ≃ₐ[S] ChartRing (e) :=
  firstNodeBranchAutomorphism (R) (U) (V) hx hy (a)
    (completeIdentityFirstActionUnit_reduction K n h i)
    (completeIdentityFirstActionReciprocalUnit_reduction K n h i)

/-- The constructed node map restricts to the full unchanged original first action. -/
theorem completeIdentityFirstActionSubalgebraNode_left :
    leftLaurentMap (e)
        (completeIdentityFirstActionSubalgebraNode K n h i hx hy (leftCoordinate (e))) =
      (U).val := by
  rw [completeIdentityFirstActionSubalgebraNode, firstNodeBranchAutomorphism_apply]
  exact congrArg Prod.fst (firstNodeBranchReconstruct_left (R) (U) (V) hx hy)

/-- Its other branch is the full reciprocal of that same original action. -/
theorem completeIdentityFirstActionSubalgebraNode_right :
    leftLaurentMap (e) (branchSwapMap (e)
        (completeIdentityFirstActionSubalgebraNode K n h i hx hy (rightCoordinate (e)))) =
      invert (U)⁻¹.val := by
  rw [completeIdentityFirstActionSubalgebraNode, firstNodeBranchAutomorphism_apply]
  exact congrArg Prod.snd (firstNodeBranchReconstruct_right (R) (U) (V) hx hy)

include hx hy in
/-- Two concrete original-coordinate membership proofs imply the unchanged positive-order law. -/
theorem completeIdentityFiniteLaw_one_of_action_subalgebra :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 := by
  let f := firstNodeBranchReconstruct (R) (U) (V) hx hy
  let hx' := firstNodeBranchLeftImage_swap (R) (U) (V) hy
  let hy' := firstNodeBranchRightImage_swap (R) (U) (V) hx
  let g := firstNodeBranchReconstruct (R) (V) (U) hx' hy'
  apply completeIdentityFiniteLaw_one_of_action_node_extensions K n h i f g
  · exact firstNodeBranchReconstruct_reduction (R) (U) (V) hx hy (a)
      (completeIdentityFirstActionUnit_reduction K n h i)
      (completeIdentityFirstActionReciprocalUnit_reduction K n h i)
  · apply firstNodeBranchReconstruct_reduction (R) (V) (U) hx' hy' (a)⁻¹
      (completeIdentityFirstActionReciprocalUnit_reduction K n h i)
    simpa only [inv_inv] using completeIdentityFirstActionUnit_reduction K n h i
  · exact congrArg Prod.fst (firstNodeBranchReconstruct_left (R) (U) (V) hx hy)
  · exact congrArg Prod.fst (firstNodeBranchReconstruct_left (R) (V) (U) hx' hy')

end FLT.Mazur.PolygonInfinitesimalStages
