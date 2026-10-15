/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstActionCoordinate
public import FLT.Mazur.PolygonCompleteIdentityObstructionBoundary
public import FLT.Mazur.PolygonFirstNodeScaledExtension

/-!
# Boundary support from extensions of the original action itself

Two node maps extending the original universal product and its reciprocal
force both missing canonical tails to vanish. The hypotheses concern the
original action, rather than extensions of a chosen conjugating coordinate.
The original node maps themselves are still a geometric construction problem.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal LaurentPolynomial PolygonChartScaling
open LaurentPositivePart LaurentBoundaryVectorField LaurentFirstStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFiniteMulObstruction
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "a" => parameterUnit K
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0
local notation "F" => completeIdentityFirstActionField K n h i
local notation "U" => completeIdentityFirstActionUnit K n h i

/-- The normalized action field detects each whole original outer error coefficient. -/
theorem completeIdentityFirstActionField_coeff_zero_iff (d : ℤ) :
    (F).coeff d = 0 ↔ (O).coeff d = 0 := by
  rw [completeIdentityFirstActionField, ← smul_eq_C_mul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  exact (coordinateUnit (1 : Kˣ))⁻¹.isUnit.mul_right_eq_zero

/-- The reciprocal original action has inverse scaling and the reciprocal computed field. -/
theorem completeIdentityFirstActionUnit_reciprocal :
    invert (U)⁻¹.val = C (a)⁻¹.val * firstOrderLaurentCoordinate (reciprocalField (F)) := by
  rw [completeIdentityFirstActionUnit_factor, mul_inv_rev, Units.val_mul, map_mul,
    firstOrderCoordinateUnit_reciprocal]
  change _ * invert (C (a)⁻¹.val) = _
  rw [invert_C, mul_comm]

variable (f g : ChartRing (parameter K[T;T⁻¹] 1) →ₐ[Ring K[T;T⁻¹] 1]
    ChartRing (parameter K[T;T⁻¹] 1))
  (hf : ∀ z, firstNodeReduction K[T;T⁻¹] (f z) =
    firstNodeReduction K[T;T⁻¹]
      (reciprocalScale (parameter K[T;T⁻¹] 1) (parameterUnit K) z))
  (hg : ∀ z, firstNodeReduction K[T;T⁻¹] (g z) =
    firstNodeReduction K[T;T⁻¹]
      (reciprocalScale (parameter K[T;T⁻¹] 1) (parameterUnit K)⁻¹ z))

include hf in
/-- An extension of the original action kills its entire nonpositive error support. -/
theorem completeIdentityFirstAction_left_support
    (hx : leftLaurentMap (e) (f (leftCoordinate (e))) = (U).val)
    (d : ℤ) (hd : d ≤ 0) : (O).coeff d = 0 := by
  apply (completeIdentityFirstActionField_coeff_zero_iff K n h i d).mp
  apply (boundaryTail_eq_zero_iff (F)).mp
    (firstNodeScaledExtension_boundaryTail_zero (a) (F) f hf ?_) d hd
  rw [hx, completeIdentityFirstActionUnit_factor, Units.val_mul]
  rfl

include hg in
/-- The reciprocal original action extension kills the original error's upper support. -/
theorem completeIdentityFirstAction_right_support
    (hx : leftLaurentMap (e) (g (leftCoordinate (e))) = invert (U)⁻¹.val)
    (d : ℤ) (hd : 2 ≤ d) : (O).coeff d = 0 := by
  have ht := firstNodeScaledExtension_boundaryTail_zero (a)⁻¹ (reciprocalField (F)) g hg
    (hx.trans (by rw [completeIdentityFirstActionUnit_reciprocal,
      firstOrderCoordinateUnit_val]))
  have he := (boundaryTail_eq_zero_iff _).mp ht (2 - d) (by omega)
  rw [reciprocalField_coeff, sub_sub_cancel, neg_eq_zero] at he
  exact (completeIdentityFirstActionField_coeff_zero_iff K n h i d).mp he

include hf hg in
/-- Genuine extensions of the original action on both boundaries imply its unchanged law. -/
theorem completeIdentityFiniteLaw_one_of_action_node_extensions
    (hl : leftLaurentMap (e) (f (leftCoordinate (e))) = (U).val)
    (hr : leftLaurentMap (e) (g (leftCoordinate (e))) = invert (U)⁻¹.val) :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  completeIdentityFiniteLaw_one_of_error_support K n h i
    (completeIdentityFirstAction_left_support K n h i f hf hl)
    (completeIdentityFirstAction_right_support K n h i g hg hr)

end FLT.Mazur.PolygonInfinitesimalStages
