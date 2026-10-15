/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstActionBoundary

/-!
# Concrete node maps for the positive parts of the original action

The two maps below are actual node automorphisms with the original universal
scaling reductions. Their full errors against the unchanged group action are
the two explicitly retained Laurent tails. Those tails are not asserted zero.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentPositivePart LaurentBoundaryVectorField
open LaurentFirstStageParameter PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "a" => parameterUnit K
local notation "F" => completeIdentityFirstActionField K n h i
local notation "U" => completeIdentityFirstActionUnit K n h i

/-- An actual original-node map with the original universal left scaling reduction. -/
def completeIdentityFirstPositiveActionLeftNode : (B) ≃ₐ[S] (B) :=
  firstNodeScaledPositiveExtension (a) (F)

/-- An actual original-node map with the original universal reciprocal scaling reduction. -/
def completeIdentityFirstPositiveActionRightNode : (B) ≃ₐ[S] (B) :=
  firstNodeScaledPositiveExtension (a)⁻¹ (reciprocalField (F))

/-- The left node map retains the original action's full prescribed closed reduction. -/
theorem completeIdentityFirstPositiveActionLeftNode_reduction (z : B) :
    firstNodeReduction (R) (completeIdentityFirstPositiveActionLeftNode K n h i z) =
      firstNodeReduction (R) (reciprocalScale (e) (a) z) :=
  firstNodeScaledPositiveExtension_reduction (a) (F) z

/-- The reciprocal node map retains its prescribed closed reduction on all functions. -/
theorem completeIdentityFirstPositiveActionRightNode_reduction (z : B) :
    firstNodeReduction (R) (completeIdentityFirstPositiveActionRightNode K n h i z) =
      firstNodeReduction (R) (reciprocalScale (e) (a)⁻¹ z) :=
  firstNodeScaledPositiveExtension_reduction (a)⁻¹ (reciprocalField (F)) z

/-- Every discrepancy with the unchanged original left action is retained in its explicit tail. -/
theorem completeIdentityFirstPositiveActionLeftNode_error :
    (U).val - leftLaurentMap (e)
        (completeIdentityFirstPositiveActionLeftNode K n h i (leftCoordinate (e))) =
      C (a).val * (C (e) * coeffMap (algebraMap (R) (S)) (boundaryTail (F))) := by
  rw [completeIdentityFirstActionUnit_factor, Units.val_mul]
  change C (a).val * (firstOrderCoordinateUnit (F)).val -
    leftLaurentMap (e) (firstNodeScaledPositiveExtension (a) (F) (leftCoordinate (e))) = _
  rw [firstNodeScaledPositiveExtension_leftLaurent, ← mul_sub]
  congr 1
  rw [← firstNodePositiveExtension_leftLaurent, firstNodePositiveExtension_error]

/-- The reciprocal error retains both the inverse scale and the reciprocal field's sign. -/
theorem completeIdentityFirstPositiveActionRightNode_error :
    invert (U)⁻¹.val - leftLaurentMap (e)
        (completeIdentityFirstPositiveActionRightNode K n h i (leftCoordinate (e))) =
      C (a)⁻¹.val *
        (C (e) * coeffMap (algebraMap (R) (S)) (boundaryTail (reciprocalField (F)))) := by
  rw [completeIdentityFirstActionUnit_reciprocal]
  change C (a)⁻¹.val * firstOrderLaurentCoordinate (reciprocalField (F)) -
    leftLaurentMap (e)
      (firstNodeScaledPositiveExtension (a)⁻¹ (reciprocalField (F)) (leftCoordinate (e))) = _
  rw [firstNodeScaledPositiveExtension_leftLaurent, ← mul_sub]
  congr 1
  rw [← firstOrderCoordinateUnit_val, ← firstNodePositiveExtension_leftLaurent,
    firstNodePositiveExtension_error]

end FLT.Mazur.PolygonInfinitesimalStages
