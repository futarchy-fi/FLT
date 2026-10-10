/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothTransportedCover

/-!
# Comparing the glued smooth affine law with boundary formulas

Descent along the pulled-back four-chart cover compares the entire smooth
transported law with the original polynomial and infinity formulas. These are
equalities of morphisms on arbitrary common schemes in arbitrary reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The entire transported smooth affine law agrees with every polynomial output chart. -/
theorem smoothAffineOverlap_polynomial (b c : Bool) (t : Fin 3) {X : Scheme.{u}}
    (f : X ⟶ (smoothAffineOverlapOpen W b c).toScheme)
    (g : X ⟶ Spec (.of
      (AdditionOutputOpen W (productChartCoordinate b) (productChartCoordinate c) t)))
    (h : f ≫ smoothAffineOverlapInput W b c = g ≫
      projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) t) :
    f ≫ smoothAffineOverlapAddition W b c ≫ (integralSmoothOpen W).ι =
      g ≫ Spec.map (CommRingCat.ofHom
        (projectiveAdditionChart W (productChartCoordinate b) (productChartCoordinate c)
          t).toRingHom) ≫ integralCurveChart W t := by
  let C : X.OpenCover := (smoothTransportedCover W b c).pullback₁ f
  apply C.hom_ext
  intro i
  let a := (smoothTransportedCover W b c).pullbackHom f i
  have ha : a ≫ (smoothTransportedCover W b c).f i = C.f i ≫ f :=
    Scheme.Cover.pullbackHom_map _ _ _
  have hi : (a ≫ smoothTransportedRawProjection W b c i) ≫ Spec.map (CommRingCat.ofHom
      (transportedAdditionInput W (productChartCoordinate b) (productChartCoordinate c)
        i).toRingHom) = (C.f i ≫ g) ≫ Spec.map (CommRingCat.ofHom
      (additionOutputRestriction W (productChartCoordinate b) (productChartCoordinate c)
        t).toRingHom) := by
    rw [Category.assoc, smoothTransportedRawProjection_inputs, ← Category.assoc, ha,
      Category.assoc, h, ← Category.assoc]
    rfl
  have he := transportedPolynomial_curve_eq_arbitrary W
    (productChartCoordinate b) (productChartCoordinate c) i t
    (a ≫ smoothTransportedRawProjection W b c i) (C.f i ≫ g) hi
  simp only [Category.assoc, smoothTransportedRawProjection_addition] at he
  rw [← Category.assoc a, ha] at he
  simpa only [Category.assoc] using he

/-- The entire transported smooth affine law agrees with the original infinity formula. -/
theorem smoothAffineOverlap_infinity {X : Scheme.{u}}
    (f : X ⟶ (smoothAffineOverlapOpen W true true).toScheme)
    (g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ smoothAffineOverlapInput W true true = g ≫ infinityAdditionInclusion W) :
    f ≫ smoothAffineOverlapAddition W true true ≫ (integralSmoothOpen W).ι =
      g ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  let C : X.OpenCover := (smoothTransportedCover W true true).pullback₁ f
  apply C.hom_ext
  intro i
  let a := (smoothTransportedCover W true true).pullbackHom f i
  have ha : a ≫ (smoothTransportedCover W true true).f i = C.f i ≫ f :=
    Scheme.Cover.pullbackHom_map _ _ _
  have hin : smoothTransportedRawProjection W true true i ≫
      Spec.map (CommRingCat.ofHom (transportedAdditionInput W 1 1 i).toRingHom) =
      (smoothTransportedCover W true true).f i ≫ smoothAffineOverlapInput W true true :=
    smoothTransportedRawProjection_inputs W true true i
  have hout : smoothTransportedRawProjection W true true i ≫
      Spec.map (CommRingCat.ofHom (transportedAdditionAffine W 1 1 i).toRingHom) ≫
        additionCurveChart W i = (smoothTransportedCover W true true).f i ≫
          smoothAffineOverlapAddition W true true ≫ (integralSmoothOpen W).ι :=
    smoothTransportedRawProjection_addition W true true i
  have hi : (a ≫ smoothTransportedRawProjection W true true i) ≫ Spec.map (CommRingCat.ofHom
      (transportedAdditionInput W 1 1 i).toRingHom) =
      (C.f i ≫ g) ≫ Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom) := by
    rw [Category.assoc, hin, ← Category.assoc, ha,
      Category.assoc, h, ← Category.assoc]
    rfl
  have he := transportedInfinity_curve_eq_arbitrary W i
    (a ≫ smoothTransportedRawProjection W true true i) (C.f i ≫ g) hi
  simp only [Category.assoc, hout] at he
  rw [← Category.assoc a, ha] at he
  simpa only [Category.assoc] using he

end FLT.Mazur.WeierstrassIntegralChart
