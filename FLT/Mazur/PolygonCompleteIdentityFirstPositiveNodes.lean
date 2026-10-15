/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodePositiveExtension
public import FLT.Mazur.PolygonCompleteIdentityFirstNodeBoundary

/-!
# Concrete first-node maps for the canonical correction and its reciprocal

The strictly positive parts of the two actual canonical boundary fields
construct two original node automorphisms. Their errors are precisely the
nonpositive tails of the original fields. Vanishing of those two explicit
tails supplies the previously missing extensions and the unchanged law.
No tail vanishing or full original node coverage is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentPositivePart LaurentBoundaryVectorField
open PolygonScalingNaturality PolygonChartScaling PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstCoordinateEquiv completeIdentityFirstCorrection
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Ring K 1
local notation "e" => parameter K 1
local notation "B" => ChartRing (e)
local notation "q" => completeIdentityFirstCorrection K n h i
local notation "u" => completeIdentityFirstCoordinateEquiv K n h i (S)[T;T⁻¹]
  (coordinateUnit (1 : (S)ˣ))

/-- A concrete original-node automorphism for the positive part of the canonical left field. -/
def completeIdentityFirstPositiveLeftNode : (B) ≃ₐ[S] (B) := firstNodePositiveExtension (q)

/-- A concrete original-node automorphism for the positive part of the reciprocal field. -/
def completeIdentityFirstPositiveRightNode : (B) ≃ₐ[S] (B) :=
  firstNodePositiveExtension (reciprocalField (q))

/-- The left map reduces to the identity on the whole original split node. -/
theorem completeIdentityFirstPositiveLeftNode_reduction (z : B) :
    firstNodeReduction K (completeIdentityFirstPositiveLeftNode K n h i z) =
      firstNodeReduction K z := firstNodePositiveExtension_reduction (q) z

/-- The reciprocal map also reduces to the identity on the whole original split node. -/
theorem completeIdentityFirstPositiveRightNode_reduction (z : B) :
    firstNodeReduction K (completeIdentityFirstPositiveRightNode K n h i z) =
      firstNodeReduction K z := firstNodePositiveExtension_reduction (reciprocalField (q)) z

/-- The first original coordinate error is the exact canonical nonpositive tail. -/
theorem completeIdentityFirstPositiveLeftNode_error :
    (u).val - leftLaurentMap (e)
        (completeIdentityFirstPositiveLeftNode K n h i (leftCoordinate (e))) =
      C (e) * coeffMap (algebraMap K (S)) (boundaryTail (q)) := by
  rw [completeIdentityFirstCoordinateEquiv_universal]
  exact firstNodePositiveExtension_error (q)

/-- The second original coordinate error retains the reciprocal tail, including its sign. -/
theorem completeIdentityFirstPositiveRightNode_error :
    invert ((u)⁻¹.val) - leftLaurentMap (e)
        (completeIdentityFirstPositiveRightNode K n h i (leftCoordinate (e))) =
      C (e) * coeffMap (algebraMap K (S)) (boundaryTail (reciprocalField (q))) := by
  rw [completeIdentityFirstCoordinateEquiv_universal, firstOrderCoordinateUnit_reciprocal]
  simpa only [firstOrderCoordinateUnit_val, completeIdentityFirstPositiveRightNode] using
    firstNodePositiveExtension_error (reciprocalField (q))

/-- Vanishing of the explicit tails makes the constructed maps the actual requested extensions. -/
theorem completeIdentityFirstCorrection_zero_of_boundaryTails
    (hl : boundaryTail (q) = 0) (hr : boundaryTail (reciprocalField (q)) = 0) : (q) = 0 := by
  apply completeIdentityFirstCorrection_zero_of_node_extensions K n h i
    (completeIdentityFirstPositiveLeftNode K n h i).toAlgHom
    (completeIdentityFirstPositiveRightNode K n h i).toAlgHom
    (completeIdentityFirstPositiveLeftNode_reduction K n h i)
    (completeIdentityFirstPositiveRightNode_reduction K n h i)
  · rw [completeIdentityFirstCoordinateEquiv_universal]
    exact (firstNodePositiveExtension_exact_iff (q)).mpr hl
  · rw [completeIdentityFirstCoordinateEquiv_universal, firstOrderCoordinateUnit_reciprocal]
    exact ((firstNodePositiveExtension_exact_iff (reciprocalField (q))).mpr hr).trans
      (firstOrderCoordinateUnit_val _)

/-- These concrete tail equations imply the unchanged original positive-order multiplication. -/
theorem completeIdentityFiniteLaw_one_of_boundaryTails
    (hl : boundaryTail (q) = 0) (hr : boundaryTail (reciprocalField (q)) = 0) :
    universalEdgeScaling (S) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  (completeIdentityFiniteLaw_one_iff_correction K n h i).mpr
    (completeIdentityFirstCorrection_zero_of_boundaryTails K n h i hl hr)

end FLT.Mazur.PolygonInfinitesimalStages
