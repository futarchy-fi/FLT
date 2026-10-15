/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstActionNodes
public import FLT.Mazur.PolygonNodeUnitBoundary

/-!
# Whole-branch scheme comparisons for the constructed original action nodes

The constructed ring automorphisms give actual automorphisms of the original
node schemes. If their explicit error tails vanish, their restrictions are
the full original action morphisms on the punctured branches, on both node
coordinates and all functions. The tail vanishing remains open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentPositivePart LaurentBoundaryVectorField
open LaurentFirstStageParameter LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstPositiveActionLeftNode completeIdentityFirstPositiveActionRightNode
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "a" => parameterUnit K
local notation "F" => completeIdentityFirstActionField K n h i
local notation "U" => completeIdentityFirstActionUnit K n h i

/-- The constructed positive left action is an automorphism of the whole original node scheme. -/
def completeIdentityFirstPositiveActionLeftIso : chart (S) (e) ≅ chart (S) (e) :=
  Scheme.Spec.mapIso
    (completeIdentityFirstPositiveActionLeftNode K n h i).toRingEquiv.toCommRingCatIso.op

/-- The reciprocal construction also acts on the whole node, including its closed point. -/
def completeIdentityFirstPositiveActionRightIso : chart (S) (e) ≅ chart (S) (e) :=
  Scheme.Spec.mapIso
    (completeIdentityFirstPositiveActionRightNode K n h i).toRingEquiv.toCommRingCatIso.op

/-- A zero left tail identifies the entire branch restriction with the original group action. -/
theorem completeIdentityFirstPositiveActionLeftIso_boundary
    (ht : boundaryTail (F) = 0) :
    leftBranchOpen (S) (e) ≫ (completeIdentityFirstPositiveActionLeftIso K n h i).hom =
      Spec.map (CommRingCat.ofHom (evalUnit (U)).toRingHom) ≫ leftBranchOpen (S) (e) := by
  apply leftBranchOpen_comp_spec_eq (e)
    (completeIdentityFirstPositiveActionLeftNode K n h i).toAlgHom (U)
  unfold completeIdentityFirstPositiveActionLeftNode
  change leftLaurentMap (e)
    (firstNodeScaledPositiveExtension (a) (F) (leftCoordinate (e))) = (U).val
  rw [firstNodeScaledPositiveExtension_exact (a) (F) ht,
    completeIdentityFirstActionUnit_factor, Units.val_mul]
  rfl

/-- A zero reciprocal tail identifies both coordinates of the full reciprocal branch square. -/
theorem completeIdentityFirstPositiveActionRightIso_boundary
    (ht : boundaryTail (reciprocalField (F)) = 0) :
    leftBranchOpen (S) (e) ≫ (completeIdentityFirstPositiveActionRightIso K n h i).hom =
      Spec.map (CommRingCat.ofHom
        (evalUnit (Units.map invert.toMonoidHom (U)⁻¹)).toRingHom) ≫
          leftBranchOpen (S) (e) := by
  apply leftBranchOpen_comp_spec_eq (e)
    (completeIdentityFirstPositiveActionRightNode K n h i).toAlgHom
    (Units.map invert.toMonoidHom (U)⁻¹)
  unfold completeIdentityFirstPositiveActionRightNode
  change leftLaurentMap (e)
    (firstNodeScaledPositiveExtension (a)⁻¹ (reciprocalField (F)) (leftCoordinate (e))) =
      invert (U)⁻¹.val
  rw [firstNodeScaledPositiveExtension_exact (a)⁻¹ (reciprocalField (F)) ht,
    completeIdentityFirstActionUnit_reciprocal, firstOrderCoordinateUnit_val]

end FLT.Mazur.PolygonInfinitesimalStages
