/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeBoundary
public import FLT.Mazur.PolygonCompleteIdentityFirstBoundary

/-!
# Original node extensions supply both canonical boundary coordinates

Endomorphisms of the two original first-order node charts, reducing to the
identity and restricting to the canonical coordinate change in the respective
Laurent coordinates, construct both polynomial extensions. Consequently they
imply the unchanged original first-order multiplication law. Constructing
these particular geometric endomorphisms remains a separate requirement.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstCoordinateEquiv completeIdentityFirstCorrection
open PolygonSmoothing PolygonChartScaling PolygonInfinitesimal LaurentPolynomial
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Ring K 1
local notation "e" => parameter K 1
local notation "B" => ChartRing (e)
local notation "u" => completeIdentityFirstCoordinateEquiv K n h i (Ring K 1)[T;T⁻¹]
  (coordinateUnit (1 : (Ring K 1)ˣ))
variable (f g : ChartRing (parameter K 1) →ₐ[Ring K 1] ChartRing (parameter K 1))
  (hf : ∀ z, firstNodeReduction K (f z) = firstNodeReduction K z)
  (hg : ∀ z, firstNodeReduction K (g z) = firstNodeReduction K z)

include hf hg

/-- Genuine node extensions force the actual canonical original correction to vanish. -/
theorem completeIdentityFirstCorrection_zero_of_node_extensions
    (hleft : leftLaurentMap (e) (f (leftCoordinate (e))) = (u).val)
    (hright : leftLaurentMap (e) (g (leftCoordinate (e))) = invert ((u)⁻¹.val)) :
    completeIdentityFirstCorrection K n h i = 0 :=
  completeIdentityFirstCorrection_zero_of_boundary K n h i
    (firstNodeBoundaryPolynomial K f hf) (firstNodeBoundaryPolynomial K g hg)
    ((firstNodeBoundaryPolynomial_toLaurent K f hf).trans hleft)
    ((firstNodeBoundaryPolynomial_toLaurent K g hg).trans hright)
    (firstNodeBoundaryPolynomial_coeff_zero K f hf)
    (firstNodeBoundaryPolynomial_coeff_zero K g hg)

/-- The unchanged original first-order multiplication follows from those actual node extensions. -/
theorem completeIdentityFiniteLaw_one_of_node_extensions
    (hleft : leftLaurentMap (e) (f (leftCoordinate (e))) = (u).val)
    (hright : leftLaurentMap (e) (g (leftCoordinate (e))) = invert ((u)⁻¹.val)) :
    universalEdgeScaling (S) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  (completeIdentityFiniteLaw_one_iff_correction K n h i).mpr
    (completeIdentityFirstCorrection_zero_of_node_extensions K n h i f g hf hg hleft hright)

end FLT.Mazur.PolygonInfinitesimalStages
