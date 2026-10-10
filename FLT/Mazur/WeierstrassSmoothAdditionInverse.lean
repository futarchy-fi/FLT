/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothLocalInverse
public import FLT.Mazur.WeierstrassInfinityInverseCover

/-!
# Two-sided inverse laws for full smooth addition

The affine and infinity inverse presentations cover the smooth curve. Their
local equalities descend globally, and involutivity supplies the other side.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The affine overlap and infinity neighborhood descend the inverse law on Y. -/
theorem smoothCurveAddition_rightNegation_yChart {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (Coordinate W 1)))
    (h : f ≫ (integralSmoothOpen W).ι = g ≫ integralCurveChart W 1) :
    f ≫ smoothProductRightNegation W ≫ smoothCurveAddition W =
      f ≫ integralSmoothStructure W ≫ integralSmoothZero W := by
  let C := infinityInverseCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hh : (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ C.f i) ≫ integralCurveChart W 1 := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ smoothProductRightNegation W ≫ smoothCurveAddition W) =
    p ≫ (f ≫ integralSmoothStructure W ≫ integralSmoothZero W)
  cases i
  · change (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ overlapInclusion W 1 2) ≫ integralCurveChart W 1 at hh
    have ha : (p ≫ f) ≫ (integralSmoothOpen W).ι =
        (q ≫ Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom)) ≫
          integralCurveChart W 2 := by
      rw [hh, Category.assoc, Category.assoc, integralCurve_output_transition]
    simpa only [Category.assoc] using
      smoothCurveAddition_rightNegation_affine W (p ≫ f) _ ha
  · change (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ infinityInverseInclusion W) ≫ integralCurveChart W 1 at hh
    simpa only [Category.assoc] using
      smoothCurveAddition_rightNegation_neighborhood W (p ≫ f) q
        (by simpa only [Category.assoc] using hh)

/-- Every smooth point plus its actual negation equals the smooth zero section. -/
@[reassoc] theorem smoothCurveAddition_right_inverse :
    smoothProductRightNegation W ≫ smoothCurveAddition W =
      integralSmoothStructure W ≫ integralSmoothZero W := by
  let C := integralCurveTwoChartCover W
  let i := (integralSmoothOpen W).ι
  apply Scheme.Cover.hom_ext (C.pullback₁ i)
  intro b
  let p := (C.pullback₁ i).f b
  let q := Scheme.Cover.pullbackHom C i b
  have hi : p ≫ i = q ≫ C.f b := (Scheme.Cover.pullbackHom_map C i b).symm
  change p ≫ (smoothProductRightNegation W ≫ smoothCurveAddition W) =
    p ≫ (integralSmoothStructure W ≫ integralSmoothZero W)
  cases b
  · exact smoothCurveAddition_rightNegation_affine W p q hi
  · exact smoothCurveAddition_rightNegation_yChart W p q hi

/-- Smooth negation is also a left inverse. -/
@[reassoc] theorem smoothCurveAddition_left_inverse :
    smoothProductLeftNegation W ≫ smoothCurveAddition W =
      integralSmoothStructure W ≫ integralSmoothZero W := by
  rw [← smoothNegation_rightGraph, Category.assoc, smoothCurveAddition_right_inverse,
    ← Category.assoc, integralSmoothNegation_structure]

/-- The actual categorical smooth product has the right inverse law. -/
@[reassoc] theorem smoothFactorAddition_right_inverse :
    smoothFactorRightNegation W ≫ smoothFactorAddition W =
      integralSmoothStructure W ≫ integralSmoothZero W := by
  rw [smoothFactorAddition, ← Category.assoc]
  exact smoothCurveAddition_right_inverse W

/-- The actual categorical smooth product has the left inverse law. -/
@[reassoc] theorem smoothFactorAddition_left_inverse :
    smoothFactorLeftNegation W ≫ smoothFactorAddition W =
      integralSmoothStructure W ≫ integralSmoothZero W := by
  rw [smoothFactorAddition, ← Category.assoc]
  exact smoothCurveAddition_left_inverse W

end FLT.Mazur.WeierstrassIntegralChart
