/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopActionRestriction
public import FLT.Mazur.PolygonCompleteIdentityTopObstructionBoundary
public import FLT.Mazur.PolygonTopNodeScaledBoundary

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
open LaurentPositivePart LaurentBoundaryVectorField LaurentStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityTopActionUnit completeIdentityTopActionField
  completeIdentityFiniteMulObstruction
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) (m + 1)
local notation "e" => parameter (R) (m + 1)
local notation "B" => ChartRing (e)
local notation "a" => parameterUnit K (m + 1)
local notation "O" => completeIdentityFiniteMulObstruction K n h i m
local notation "F" => completeIdentityTopActionField K n h i m
local notation "U" => completeIdentityTopActionUnit K n h i m

/-- The normalized action field detects each whole original outer error coefficient. -/
theorem completeIdentityTopActionField_coeff_zero_iff (d : ℤ) :
    (F).coeff d = 0 ↔ (O).coeff d = 0 := by
  rw [completeIdentityTopActionField, ← smul_eq_C_mul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  exact (coordinateUnit (1 : Kˣ))⁻¹.isUnit.mul_right_eq_zero

variable (f g : ChartRing (parameter K[T;T⁻¹] (m + 1)) →ₐ[Ring K[T;T⁻¹] (m + 1)]
    ChartRing (parameter K[T;T⁻¹] (m + 1)))
  (hf : ∀ z, topNodeRestriction K[T;T⁻¹] m (f z) =
    topNodeRestriction K[T;T⁻¹] m
      (reciprocalScale (parameter K[T;T⁻¹] (m + 1)) (parameterUnit K (m + 1)) z))
  (hg : ∀ z, topNodeRestriction K[T;T⁻¹] m (g z) =
    topNodeRestriction K[T;T⁻¹] m
      (reciprocalScale (parameter K[T;T⁻¹] (m + 1)) (parameterUnit K (m + 1))⁻¹ z))

variable (hm : completeIdentityFiniteMulDefect K n h i m = 0)

include hm hf in
/-- An extension of the original action kills its entire nonpositive error support. -/
theorem completeIdentityTopAction_left_support
    (hx : leftLaurentMap (e) (f (leftCoordinate (e))) = (U).val)
    (d : ℤ) (hd : d ≤ 0) : (O).coeff d = 0 := by
  apply (completeIdentityTopActionField_coeff_zero_iff K n h i m d).mp
  apply (boundaryTail_eq_zero_iff (F)).mp
    (topNodeScaledExtension_boundaryTail_zero (R) m (a) f hf (F) ?_) d hd
  rw [hx, completeIdentityTopActionUnit_factor K n h i m hm, Units.val_mul]
  rfl

include hm hg in
/-- The reciprocal original action extension kills the original error's upper support. -/
theorem completeIdentityTopAction_right_support
    (hx : leftLaurentMap (e) (g (leftCoordinate (e))) = invert (U)⁻¹.val)
    (d : ℤ) (hd : 2 ≤ d) : (O).coeff d = 0 := by
  have ht := topNodeScaledExtension_boundaryTail_zero (R) m (a)⁻¹ g hg (reciprocalField (F))
    (hx.trans (by rw [completeIdentityTopActionUnit_reciprocal K n h i m hm,
      topOrderCoordinateUnit_val]))
  have he := (boundaryTail_eq_zero_iff _).mp ht (2 - d) (by omega)
  rw [reciprocalField_coeff, sub_sub_cancel, neg_eq_zero] at he
  exact (completeIdentityTopActionField_coeff_zero_iff K n h i m d).mp he

include hm hf hg in
/-- Genuine extensions of the original action on both boundaries imply its unchanged law. -/
theorem completeIdentityFiniteLaw_succ_of_action_node_extensions
    (hl : leftLaurentMap (e) (f (leftCoordinate (e))) = (U).val)
    (hr : leftLaurentMap (e) (g (leftCoordinate (e))) = invert (U)⁻¹.val) :
    universalEdgeScaling (Ring K (m + 1)) ≫ completeIdentityStageTorus K n h i (m + 1) =
      completeIdentityFiniteOriginalMul K n h i (m + 1) :=
  completeIdentityFiniteLaw_succ_of_error_support K n h i m hm
    (completeIdentityTopAction_left_support K n h i m f hf hm hl)
    (completeIdentityTopAction_right_support K n h i m g hg hm hr)

end FLT.Mazur.PolygonInfinitesimalStages
