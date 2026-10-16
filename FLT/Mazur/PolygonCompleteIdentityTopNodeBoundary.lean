/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeBoundary
public import FLT.Mazur.PolygonCompleteIdentityTopBoundary
public import FLT.Mazur.PolygonCompleteIdentitySecondCorrection

/-!
# Original node extensions supply both canonical boundary coordinates

Endomorphisms of the two original next-order node charts, restricting to the
identity at the preceding stage and restricting to the canonical coordinate change in the respective
Laurent coordinates, construct both polynomial extensions. Consequently they
imply the unchanged original next-order multiplication law. Constructing
these particular geometric endomorphisms remains a separate requirement.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityTopCoordinateEquiv completeIdentityTopCorrection
open PolygonSmoothing PolygonChartScaling PolygonInfinitesimal LaurentPolynomial
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "S" => Ring K (m + 1)
local notation "e" => parameter K (m + 1)
local notation "B" => ChartRing (e)
local notation "u" => completeIdentityTopCoordinateEquiv K n h i m (Ring K (m + 1))[T;T⁻¹]
  (coordinateUnit (1 : (Ring K (m + 1))ˣ))
variable (f g : ChartRing (parameter K (m + 1)) →ₐ[Ring K (m + 1)] ChartRing (parameter K (m + 1)))
  (hf : ∀ z, topNodeRestriction K m (f z) = topNodeRestriction K m z)
  (hg : ∀ z, topNodeRestriction K m (g z) = topNodeRestriction K m z)

variable (hm : completeIdentityFiniteMulDefect K n h i m = 0)

include hf hg hm

/-- Genuine node extensions force the actual canonical original correction to vanish. -/
theorem completeIdentityTopCorrection_zero_of_node_extensions
    (hleft : leftLaurentMap (e) (f (leftCoordinate (e))) = (u).val)
    (hright : leftLaurentMap (e) (g (leftCoordinate (e))) = invert ((u)⁻¹.val)) :
    completeIdentityTopCorrection K n h i m = 0 :=
  completeIdentityTopCorrection_zero_of_boundary K n h i m hm
    (topNodeBoundaryPolynomial K m f hf) (topNodeBoundaryPolynomial K m g hg)
    ((topNodeBoundaryPolynomial_toLaurent K m f hf).trans hleft)
    ((topNodeBoundaryPolynomial_toLaurent K m g hg).trans hright)
    (topNodeBoundaryPolynomial_coeff_zero K m f hf)
    (topNodeBoundaryPolynomial_coeff_zero K m g hg)

/-- The unchanged original next-order multiplication follows from those actual node extensions. -/
theorem completeIdentityFiniteLaw_succ_of_node_extensions
    (hleft : leftLaurentMap (e) (f (leftCoordinate (e))) = (u).val)
    (hright : leftLaurentMap (e) (g (leftCoordinate (e))) = invert ((u)⁻¹.val)) :
    universalEdgeScaling (S) ≫ completeIdentityStageTorus K n h i (m + 1) =
      completeIdentityFiniteOriginalMul K n h i (m + 1) :=
  (completeIdentityFiniteLaw_succ_iff_correction K n h i m hm).mpr
    (completeIdentityTopCorrection_zero_of_node_extensions K n h i m f g hf hg hm hleft hright)

end FLT.Mazur.PolygonInfinitesimalStages

namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonChartScaling PolygonInfinitesimal LaurentPolynomial
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "e" => parameter K 2
local notation "u" => completeIdentityTopCoordinateEquiv K n h 0 1 (Ring K 2)[T;T⁻¹]
  (coordinateUnit (1 : (Ring K 2)ˣ))
variable (f g : ChartRing (parameter K 2) →ₐ[Ring K 2] ChartRing (parameter K 2))
  (hf : ∀ z, topNodeRestriction K 1 (f z) = topNodeRestriction K 1 z)
  (hg : ∀ z, topNodeRestriction K 1 (g z) = topNodeRestriction K 1 z)

include hf hg

/-- The proved first law leaves only the two actual node extensions at second order. -/
theorem completeIdentitySecondCorrection_zero_of_node_extensions
    (hleft : leftLaurentMap (e) (f (leftCoordinate (e))) = (u).val)
    (hright : leftLaurentMap (e) (g (leftCoordinate (e))) = invert ((u)⁻¹.val)) :
    completeIdentityTopCorrection K n h 0 1 = 0 :=
  completeIdentityTopCorrection_zero_of_node_extensions K n h 0 1 f g hf hg
    (completeIdentityFiniteMulDefect_firstPositive K n h) hleft hright

/-- Those actual extensions give the full second-stage comparison, including every node. -/
theorem completeIdentityFiniteComparison_second_of_node_extensions
    (hleft : leftLaurentMap (e) (f (leftCoordinate (e))) = (u).val)
    (hright : leftLaurentMap (e) (g (leftCoordinate (e))) = invert ((u)⁻¹.val)) :
    completeIdentityFiniteScaling K n h 2 ≫ completePointToIntegralCubic K n h 0 =
      completeIdentityFiniteInput K n h 0 2 ≫ completeIdentityActionTarget K n h 0 :=
  (completeIdentityFiniteComparison_second_iff_correction K n h).mpr
    (completeIdentitySecondCorrection_zero_of_node_extensions K n h f g hf hg hleft hright)

end FLT.Mazur.PolygonInfinitesimalStages
