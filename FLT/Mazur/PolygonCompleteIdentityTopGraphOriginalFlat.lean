/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopGraphAlgebra
public import FLT.Mazur.PolygonTopNodeGraphOriginalFlat

/-!
# Original-base flatness criterion for the actual higher action

The coefficient map is the unchanged map from the original truncated base
to the actual source-target graph. Its flatness constructs a full original
node map with both prescribed action branches. Proving this geometric
flatness remains necessary; no substitute multiplication law is used.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) (m + 1)
local notation "e" => parameter (R) (m + 1)
local notation "L" => (S)[T;T⁻¹]
local notation "B" => ChartRing (e)
local notation "C" => stageNodeBranchSubalgebra (R) (m + 1)
local notation "U" => completeIdentityTopActionUnit K n h i m
local notation "V" => completeIdentityTopActionReciprocalUnit K n h i m
local notation "a" => parameterUnit K (m + 1)
local notation "G" => completeIdentityTopGraphAlgebra K n h i m

/-- The original smaller truncated-base coefficient map of the actual graph. -/
def completeIdentityTopGraphOriginalScalars : Ring K (m + 1) →+* (G) :=
  topNodeGraphOriginalScalars (R) m (U) (V) (LaurentPolynomial.C : K →+* R)

/-- The map retains the actual smoothing parameter, without changing the base. -/
theorem completeIdentityTopGraphOriginalScalars_parameter :
    completeIdentityTopGraphOriginalScalars K n h i m (parameter K (m + 1)) =
      algebraMap (S) (G) (e) :=
  topNodeGraphOriginalScalars_parameter (R) m (U) (V) (LaurentPolynomial.C : K →+* R)

variable (hm : completeIdentityFiniteMulDefect K n h i m = 0)
  (hf : (completeIdentityTopGraphOriginalScalars K n h i m).Flat)
include hm hf

/-- Original-base flatness descends every full actual multiplication defect. -/
theorem completeIdentityTopGraphOriginalFlat_defect (z : B) :
    completeIdentityTopActionNodeDefect K n h i m z ∈ (C) :=
  topNodeGraphOriginalFlat_defect (R) m (U) (V) (a) (LaurentPolynomial.C : K →+* R)
    (completeIdentityTopActionUnit_restriction K n h i m hm)
    (completeIdentityTopActionReciprocalUnit_restriction K n h i m hm) hf z

/-- Flatness of this precise coefficient map preserves the whole original node algebra. -/
theorem completeIdentityTopGraphOriginalFlat_preserves
    (p : (L) × (L)) (hp : p ∈ (C)) :
    stageNodeBranchSubstitution (R) (m + 1) (U) (V) p ∈ (C) :=
  topNodeGraphOriginalFlat_preserves (R) m (U) (V) (a) (LaurentPolynomial.C : K →+* R)
    (completeIdentityTopActionUnit_restriction K n h i m hm)
    (completeIdentityTopActionReciprocalUnit_restriction K n h i m hm) hf p hp

/-- The same original-base hypothesis yields flatness over all retained Laurent coefficients. -/
theorem completeIdentityTopGraphOriginalFlat_laurent : Module.Flat (S) (G) :=
  topNodeGraphOriginalFlat_coefficients (R) m (U) (V) (a) (LaurentPolynomial.C : K →+* R)
    (completeIdentityTopActionUnit_restriction K n h i m hm)
    (completeIdentityTopActionReciprocalUnit_restriction K n h i m hm) hf

/-- Both actual coordinate pairs descend under the single geometric flatness premise. -/
theorem completeIdentityTopGraphOriginalFlat_coordinates :
    stageNodeBranchLeftImage (R) (m + 1) (U) (V) ∈ (C) ∧
      stageNodeBranchRightImage (R) (m + 1) (U) (V) ∈ (C) :=
  (stageNodeBranchSubstitution_preserves_iff (R) (m + 1) (U) (V)).mp
    (completeIdentityTopGraphOriginalFlat_preserves K n h i m hm hf)

/-- Construct the full original node map from flatness of its actual finite graph. -/
def completeIdentityTopGraphOriginalFlatNode : (B) →ₐ[S] (B) :=
  stageNodeBranchReconstruct (R) (m + 1) (U) (V)
    (completeIdentityTopGraphOriginalFlat_coordinates K n h i m hm hf).1
    (completeIdentityTopGraphOriginalFlat_coordinates K n h i m hm hf).2

/-- Its first branch is the unchanged original universal multiplication unit. -/
theorem completeIdentityTopGraphOriginalFlatNode_left :
    leftLaurentMap (e)
      (completeIdentityTopGraphOriginalFlatNode K n h i m hm hf (leftCoordinate (e))) =
        (U).val :=
  congrArg Prod.fst (stageNodeBranchReconstruct_left (R) (m + 1) (U) (V) _ _)

/-- Its other branch is the exact reciprocal of that same original action. -/
theorem completeIdentityTopGraphOriginalFlatNode_right :
    leftLaurentMap (e) (branchSwapMap (e)
      (completeIdentityTopGraphOriginalFlatNode K n h i m hm hf (rightCoordinate (e)))) =
        invert (U)⁻¹.val :=
  congrArg Prod.snd (stageNodeBranchReconstruct_right (R) (m + 1) (U) (V) _ _)

end FLT.Mazur.PolygonInfinitesimalStages
