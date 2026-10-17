/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopGraphOriginalFlat
public import FLT.Mazur.PolygonCompleteIdentityTopActionBoundary
public import FLT.Mazur.PolygonTopNodeBranchRestriction

/-!
# Original higher graph flatness supplies both actual action boundaries

Reconstruct both orientations of the original node from the retained branch
pairs. Their preceding restrictions are the prescribed inverse scalings.
The resulting support bounds kill the actual canonical higher correction.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) (m + 1)
local notation "U" => completeIdentityTopActionUnit K n h i m
local notation "V" => completeIdentityTopActionReciprocalUnit K n h i m
local notation "a" => parameterUnit K (m + 1)
variable (hm : completeIdentityFiniteMulDefect K n h i m = 0)
  (hf : (completeIdentityTopGraphOriginalScalars K n h i m).Flat)
include hm hf

/-- The actual original graph supplies the next law through its two full node extensions. -/
theorem completeIdentityFiniteLaw_succ_of_graphOriginalFlat :
    universalEdgeScaling (Ring K (m + 1)) ≫ completeIdentityStageTorus K n h i (m + 1) =
      completeIdentityFiniteOriginalMul K n h i (m + 1) := by
  obtain ⟨hx, hy⟩ := completeIdentityTopGraphOriginalFlat_coordinates K n h i m hm hf
  let f := stageNodeBranchReconstruct (R) (m + 1) (U) (V) hx hy
  have hx' := topNodeBranchLeftImage_swap (R) m (U) (V) hy
  have hy' := topNodeBranchRightImage_swap (R) m (U) (V) hx
  let g := stageNodeBranchReconstruct (R) (m + 1) (V) (U) hx' hy'
  have hu := completeIdentityTopActionUnit_restriction K n h i m hm
  have hv := completeIdentityTopActionReciprocalUnit_restriction K n h i m hm
  apply completeIdentityFiniteLaw_succ_of_action_node_extensions K n h i m f g
    (topNodeBranchReconstruct_restriction (R) m (U) (V) hx hy (a) hu hv)
    (topNodeBranchReconstruct_restriction (R) m (V) (U) hx' hy' (a)⁻¹ hv
      (by simpa only [inv_inv] using hu)) hm
  · exact congrArg Prod.fst (stageNodeBranchReconstruct_left (R) (m + 1) (U) (V) hx hy)
  · exact congrArg Prod.fst (stageNodeBranchReconstruct_left (R) (m + 1) (V) (U) hx' hy')

/-- The correction of the unchanged multiplication vanishes under actual graph flatness. -/
theorem completeIdentityTopCorrection_zero_of_graphOriginalFlat :
    completeIdentityTopCorrection K n h i m = 0 :=
  (completeIdentityFiniteLaw_succ_iff_correction K n h i m hm).mp
    (completeIdentityFiniteLaw_succ_of_graphOriginalFlat K n h i m hm hf)

end FLT.Mazur.PolygonInfinitesimalStages
