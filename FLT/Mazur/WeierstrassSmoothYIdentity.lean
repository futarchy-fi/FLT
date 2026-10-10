/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothInfinityIdentity
public import FLT.Mazur.WeierstrassSmoothAffineIdentity
public import FLT.Mazur.WeierstrassInfinityIdentityCover

/-!
# Identity laws for arbitrary smooth Y-chart presentations

The concrete infinity neighborhoods retain both identity laws under the
full smooth addition, on arbitrary common schemes and over every base ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The affine overlap and infinity neighborhood descend the left identity on Y. -/
theorem smoothCurveAddition_leftZero_yChart {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (Coordinate W 1)))
    (h : f ≫ (integralSmoothOpen W).ι = g ≫ integralCurveChart W 1) :
    f ≫ smoothProductLeftZero W ≫ smoothCurveAddition W = f := by
  let C := infinityIdentityCover W true
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hh : (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ C.f i) ≫ integralCurveChart W 1 := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ smoothProductLeftZero W ≫ smoothCurveAddition W) = p ≫ f
  cases i
  · change (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ overlapInclusion W 1 2) ≫ integralCurveChart W 1 at hh
    have ha : (p ≫ f) ≫ (integralSmoothOpen W).ι =
        (q ≫ Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom)) ≫
          integralCurveChart W 2 := by
      rw [hh, Category.assoc, Category.assoc, integralCurve_output_transition]
    simpa only [Category.assoc] using
      smoothCurveAddition_leftZero_affine W (p ≫ f) _ ha
  · change (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ infinityIdentityInclusion W true) ≫ integralCurveChart W 1 at hh
    simpa only [Category.assoc] using
      smoothCurveAddition_leftZero_neighborhood W (p ≫ f) q
        (by simpa only [Category.assoc] using hh)

/-- The affine overlap and infinity neighborhood descend the right identity on Y. -/
theorem smoothCurveAddition_rightZero_yChart {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (Coordinate W 1)))
    (h : f ≫ (integralSmoothOpen W).ι = g ≫ integralCurveChart W 1) :
    f ≫ smoothProductRightZero W ≫ smoothCurveAddition W = f := by
  let C := infinityIdentityCover W false
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hh : (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ C.f i) ≫ integralCurveChart W 1 := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ smoothProductRightZero W ≫ smoothCurveAddition W) = p ≫ f
  cases i
  · change (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ overlapInclusion W 1 2) ≫ integralCurveChart W 1 at hh
    have ha : (p ≫ f) ≫ (integralSmoothOpen W).ι =
        (q ≫ Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom)) ≫
          integralCurveChart W 2 := by
      rw [hh, Category.assoc, Category.assoc, integralCurve_output_transition]
    simpa only [Category.assoc] using
      smoothCurveAddition_rightZero_affine W (p ≫ f) _ ha
  · change (p ≫ f) ≫ (integralSmoothOpen W).ι =
      (q ≫ infinityIdentityInclusion W false) ≫ integralCurveChart W 1 at hh
    simpa only [Category.assoc] using
      smoothCurveAddition_rightZero_neighborhood W (p ≫ f) q
        (by simpa only [Category.assoc] using hh)

end FLT.Mazur.WeierstrassIntegralChart
