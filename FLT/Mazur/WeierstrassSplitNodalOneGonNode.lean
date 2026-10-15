/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalOneGonCoordinates
public import FLT.Mazur.WeierstrassSplitNodalObstruction

/-!
# The pinched node is the original nodal cubic origin

The full one-gon comparison sends the specified pinching node to [0:0:1].
This is equality of scheme morphisms, retaining the original affine origin
evaluation rather than only the underlying singular point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] (a : Kˣ)

/-- The actual affine origin of the original split nodal projective cubic. -/
def splitNodalOrigin : Spec (.of K) ⟶ integralCurve (splitNodalEquation a) :=
  Spec.map (CommRingCat.ofHom (splitNodalOriginEval a).toRingHom) ≫
    integralCurveChart (splitNodalEquation a) 2

/-- The origin evaluation retains exactly its original homogeneous coordinates. -/
@[reassoc] theorem splitNodalOrigin_projectivePoint :
    splitNodalOrigin a ≫ integralProjectiveMap (splitNodalEquation a) =
      ProjectiveSpace.unitChartPoint K (Fin 3) (RingHom.id K) ![0, 0, 1] 2 1 rfl := by
  rw [splitNodalOrigin, Category.assoc, integralCurveChart_projectiveMap,
    projectiveChartMap_eq_unitChartPoint, ProjectiveSpace.unitChartPoint_map]
  simp only [map_one]
  congr 1
  · exact (splitNodalOriginEval a).comp_algebraMap
  · funext i
    exact splitNodalOriginEval_coord a i

/-- The original pinching node has the origin tuple on the zero-parameter cubic. -/
@[reassoc] theorem zeroFiberIso_node_projectivePoint :
    PolygonNodePresentation.bOrigin K ≫ OneGonGluing.node K ≫
        (OneGonSmoothing.zeroFiberIso K).hom ≫
          integralProjectiveMap (OneGonSmoothing.equation (0 : K)) =
      ProjectiveSpace.unitChartPoint K (Fin 3) (RingHom.id K) ![0, 0, 1] 2 1 rfl := by
  rw [OneGonSmoothing.node_zeroFiberIso_assoc, OneGonSmoothing.zeroNodeInclusion,
    Category.assoc, integralCurveChart_projectiveMap, projectiveChartMap_eq_unitChartPoint]
  change Spec.map (CommRingCat.ofHom PolygonNodePresentation.bEval.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (OneGonSmoothing.zeroAffineNodeEquiv K).toRingHom) ≫ _ = _
  rw [← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom ((PolygonNodePresentation.bEval.comp
    (OneGonSmoothing.zeroAffineNodeEquiv K).toAlgHom).toRingHom)) ≫ _ = _
  rw [ProjectiveSpace.unitChartPoint_map]
  simp only [map_one]
  congr 1
  · apply RingHom.ext
    intro r
    exact (PolygonNodePresentation.bEval.comp
      (OneGonSmoothing.zeroAffineNodeEquiv K).toAlgHom).commutes r
  · funext i
    fin_cases i <;> simp [PolygonNodePresentation.bEval, PolygonNodePresentation.u,
      PolygonNodePresentation.v]

/-- The homogeneous unit scaling fixes the affine node tuple. -/
theorem splitNodalOneGonChange_origin :
    ProjectiveSpace.unitChartPoint K (Fin 3) (RingHom.id K) ![0, 0, 1] 2 1 rfl ≫
        (WeierstrassVariableChangeLinear.projectiveIso (splitNodalOneGonChange a)).hom =
      ProjectiveSpace.unitChartPoint K (Fin 3) (RingHom.id K) ![0, 0, 1] 2 1 rfl := by
  have hc : WeierstrassVariableChangeHomogeneous.coordinates
      (splitNodalOneGonChange a) ![0, 0, 1] = ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp [WeierstrassVariableChangeHomogeneous.coordinates,
      splitNodalOneGonChange]
  have h := WeierstrassVariableChangeLinear.unitChartPoint_projectiveIso
    (splitNodalOneGonChange a) (RingHom.id K) ![0, 0, 1] 2 2 1 1 rfl
    (by simp [VariableChange.map_id, hc])
  simpa only [VariableChange.map_id, hc] using h

/-- The full comparison sends the original pinching node to the original cubic origin. -/
@[reassoc] theorem splitNodalOneGonIso_node :
    PolygonNodePresentation.bOrigin K ≫ OneGonGluing.node K ≫
      (splitNodalOneGonIso a).hom = splitNodalOrigin a := by
  apply (cancel_mono (integralProjectiveMap (splitNodalEquation a))).mp
  simp only [splitNodalOneGonIso, Iso.trans_hom, Category.assoc]
  change _ ≫ _ ≫ _ ≫ integralVariableChangeTo _ _ _ _ ≫ _ = _
  rw [integralVariableChangeTo_projectiveMap, zeroFiberIso_node_projectivePoint_assoc,
    splitNodalOneGonChange_origin, splitNodalOrigin_projectivePoint]

end FLT.Mazur.WeierstrassIntegralChart
