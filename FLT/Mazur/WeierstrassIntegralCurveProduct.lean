/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover
public import FLT.Mazur.WeierstrassProductOverlapScheme

/-!
# Tensor charts on the actual integral cubic product

The four Y/Z chart products form an open cover of the fiber product of the
glued curve over its coefficient spectrum. Their rings are the exact
ChartProduct rings used by the previously constructed local addition laws.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual product of the integral cubic over the coefficient spectrum. -/
abbrev integralCurveProduct := pullback (integralCurveStructure W) (integralCurveStructure W)

/-- The Y/Z product cover before the tensor-spectrum identification. -/
def integralCurveProductPullbackCover : (integralCurveProduct W).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (integralCurveTwoChartCover W)
    (integralCurveTwoChartCover W) (integralCurveStructure W) (integralCurveStructure W)

/-- The two homogeneous coordinate indices of a product chart. -/
def productChartCoordinate (b : Bool) : Fin 3 := if b then 1 else 2

/-- Every member is the spectrum of the existing integral chart product ring. -/
def integralCurveProductChartIso (b c : Bool) :
    (integralCurveProductPullbackCover W).X (b, c) ≅
      Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) :=
  pullback.congrHom (integralCurveChart_structure W (productChartCoordinate b))
      (integralCurveChart_structure W (productChartCoordinate c)) ≪≫
    pullbackSpecIso R (Coordinate W (productChartCoordinate b))
      (Coordinate W (productChartCoordinate c))

/-- The tensor chart inclusion into the actual curve product. -/
def integralCurveProductChart (b c : Bool) :
    Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) ⟶
      integralCurveProduct W :=
  (integralCurveProductChartIso W b c).inv ≫
    (integralCurveProductPullbackCover W).f (b, c)

instance integralCurveProductChart_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (integralCurveProductChart W b c) := by
  unfold integralCurveProductChart
  infer_instance

/-- The first input of a tensor chart is its original first coordinate. -/
theorem integralCurveProductChart_fst (b c : Bool) :
    integralCurveProductChart W b c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (chartProductLeft W (productChartCoordinate b) (productChartCoordinate c)).toRingHom) ≫
        integralCurveChart W (productChartCoordinate b) := by
  simp [integralCurveProductChart, integralCurveProductChartIso,
    integralCurveProductPullbackCover, Scheme.Pullback.openCoverOfLeftRight_f,
    integralCurveTwoChartCover, chartProductLeft, chartStructure, productChartCoordinate,
    Algebra.TensorProduct.includeLeft]

/-- The second input of a tensor chart is its original second coordinate. -/
theorem integralCurveProductChart_snd (b c : Bool) :
    integralCurveProductChart W b c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (chartProductRight W (productChartCoordinate b) (productChartCoordinate c)).toRingHom) ≫
        integralCurveChart W (productChartCoordinate c) := by
  simp [integralCurveProductChart, integralCurveProductChartIso,
    integralCurveProductPullbackCover, Scheme.Pullback.openCoverOfLeftRight_f,
    integralCurveTwoChartCover, chartProductRight, chartStructure, productChartCoordinate]

/-- The four concrete tensor spectra cover the entire actual curve product. -/
def integralCurveProductCover : (integralCurveProduct W).OpenCover :=
  (integralCurveProductPullbackCover W).copy (Bool × Bool)
    (fun p => Spec (.of (ChartProduct W
      (productChartCoordinate p.1) (productChartCoordinate p.2))))
    (fun p => integralCurveProductChart W p.1 p.2) (Equiv.refl _)
    (fun p => (integralCurveProductChartIso W p.1 p.2).symm) (fun _ => rfl)

end FLT.Mazur.WeierstrassIntegralChart
