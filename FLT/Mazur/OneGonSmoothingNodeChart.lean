/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingAffinePresentation
public import FLT.Mazur.OneGonGluing
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# Identification with the original pinched one-gon chart

This comparison uses the endpoint equalizer algebra itself. Both original
coordinate functions and the coefficient structure map are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open PolygonNodePresentation WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K]

/-- The actual zero-parameter affine chart is the original endpoint equalizer. -/
def zeroAffineNodeEquiv : Coordinate (equation (0 : K)) 2 ≃ₐ[K] B (R := K) :=
  zeroAffinePlaneEquiv.trans bQuotientEquiv

/-- The original pinching presentation retains its first coordinate. -/
theorem planeToNode_x : bQuotientEquiv (planeCoord (R := K) 0) = u := by
  change bPresent (MvPolynomial.X 0) = u
  exact bPresent_X_zero

/-- The original pinching presentation retains its second coordinate. -/
theorem planeToNode_y : bQuotientEquiv (planeCoord (R := K) 1) = v := by
  change bPresent (MvPolynomial.X 1) = v
  exact bPresent_X_one

/-- The normalized affine x coordinate is the original function u. -/
@[simp] theorem zeroAffineNodeEquiv_x :
    zeroAffineNodeEquiv K (coord (equation (0 : K)) 2 0) = u := by
  change bQuotientEquiv
    (zeroAffinePlaneEquiv (coord (equation (0 : K)) 2 0)) = u
  rw [zeroAffinePlaneEquiv_x, planeToNode_x]

/-- The normalized affine y coordinate is the original function v. -/
@[simp] theorem zeroAffineNodeEquiv_y :
    zeroAffineNodeEquiv K (coord (equation (0 : K)) 2 1) = v := by
  change bQuotientEquiv
    (zeroAffinePlaneEquiv (coord (equation (0 : K)) 2 1)) = v
  rw [zeroAffinePlaneEquiv_y, planeToNode_y]

/-- The inverse retains u as the original affine x coordinate. -/
@[simp] theorem zeroAffineNodeEquiv_symm_u :
    (zeroAffineNodeEquiv K).symm u = coord (equation (0 : K)) 2 0 := by
  apply (zeroAffineNodeEquiv K).injective
  simp

/-- The inverse retains v as the original affine y coordinate. -/
@[simp] theorem zeroAffineNodeEquiv_symm_v :
    (zeroAffineNodeEquiv K).symm v = coord (equation (0 : K)) 2 1 := by
  apply (zeroAffineNodeEquiv K).injective
  simp

/-- The original node chart and the zero-parameter affine chart are isomorphic. -/
def zeroNodeChartIso : OneGonGluing.nodeChart K ≅ chartScheme (equation (0 : K)) 2 :=
  Scheme.Spec.mapIso (zeroAffineNodeEquiv K).toRingEquiv.toCommRingCatIso.op

/-- The chart identification preserves the original map to the coefficient field. -/
@[reassoc] theorem zeroNodeChartIso_structure :
    (zeroNodeChartIso K).hom ≫ chartStructure (equation (0 : K)) 2 = bToBase K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (zeroAffineNodeEquiv K).commutes

/-- Include the original pinched chart in the actual zero-parameter cubic. -/
def zeroNodeInclusion : OneGonGluing.nodeChart K ⟶ integralCurve (equation (0 : K)) :=
  (zeroNodeChartIso K).hom ≫ integralCurveChart (equation (0 : K)) 2

/-- The constructed inclusion is open. -/
instance zeroNodeInclusion_isOpenImmersion : IsOpenImmersion (zeroNodeInclusion K) := by
  dsimp [zeroNodeInclusion]
  infer_instance

/-- The inclusion of the original pinched chart lies over the original base. -/
@[reassoc] theorem zeroNodeInclusion_structure :
    zeroNodeInclusion K ≫ integralCurveStructure (equation (0 : K)) = bToBase K := by
  rw [zeroNodeInclusion, Category.assoc, integralCurveChart_structure,
    zeroNodeChartIso_structure]

end FLT.Mazur.OneGonSmoothing
