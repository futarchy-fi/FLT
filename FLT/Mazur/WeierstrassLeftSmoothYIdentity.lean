/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInfinityIdentity
public import FLT.Mazur.WeierstrassLeftSmoothAffineIdentity
public import FLT.Mazur.WeierstrassInfinityIdentityCover

/-!
# Zero fixes every original Y-chart point

The affine overlap and infinity neighborhood cover the entire Y chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The affine overlap and infinity neighborhood descend the left identity on Y. -/
theorem leftSmoothCurveAddition_leftZero_yChart {X : Scheme.{u}}
    (f : X ⟶ integralCurve W)
    (g : X ⟶ Spec (.of (Coordinate W 1)))
    (h : f = g ≫ integralCurveChart W 1) :
    f ≫ leftSmoothProductZero W ≫ leftSmoothCurveAddition W = f := by
  let C := infinityIdentityCover W true
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hh : (p ≫ f) =
      (q ≫ C.f i) ≫ integralCurveChart W 1 := by
    rw [h, ← Category.assoc, hi]
  change p ≫ (f ≫ leftSmoothProductZero W ≫ leftSmoothCurveAddition W) = p ≫ f
  cases i
  · change (p ≫ f) =
      (q ≫ overlapInclusion W 1 2) ≫ integralCurveChart W 1 at hh
    have ha : (p ≫ f) =
        (q ≫ Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom)) ≫
          integralCurveChart W 2 := by
      rw [hh, Category.assoc, Category.assoc, integralCurve_output_transition]
    simpa only [Category.assoc] using
      leftSmoothCurveAddition_leftZero_affine W (p ≫ f) _ ha
  · change (p ≫ f) =
      (q ≫ infinityIdentityInclusion W true) ≫ integralCurveChart W 1 at hh
    simpa only [Category.assoc] using
      leftSmoothCurveAddition_leftZero_neighborhood W (p ≫ f) q
        (by simpa only [Category.assoc] using hh)

end FLT.Mazur.WeierstrassIntegralChart
