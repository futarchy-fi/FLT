/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAdditionOriginalFormulas
public import FLT.Mazur.WeierstrassSmoothZeroGraphs
public import FLT.Mazur.WeierstrassGlobalAdditionZeroRestrictions

/-!
# The identity laws for every smooth affine point

The original polynomial identity calculations apply to the new global smooth
addition on arbitrary schemes presenting affine points. No reducedness or
good reduction hypothesis is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Zero on the left fixes any smooth point with an affine presentation. -/
theorem smoothCurveAddition_leftZero_affine {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (Coordinate W 2)))
    (h : f ≫ (integralSmoothOpen W).ι = g ≫ integralCurveChart W 2) :
    f ≫ smoothProductLeftZero W ≫ smoothCurveAddition W = f := by
  have hi : (f ≫ smoothProductLeftZero W) ≫ (smoothCurveProductOpen W).ι =
      (g ≫ Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom)) ≫
        projectiveAdditionInclusion W 1 2 2 ≫ integralCurveProductChart W true false := by
    rw [Category.assoc, smoothProductLeftZero_inclusion, ← Category.assoc, h, Category.assoc]
    have hc : integralCurveChart W 2 ≫ integralCurveLeftZero W =
        Spec.map (CommRingCat.ofHom (chartProductAtLeftInfinity W 2).toRingHom) ≫
          integralCurveProductChart W true false := integralCurveChart_leftZero W false
    rw [hc]
    simpa only [Category.assoc] using
      congrArg (fun a => g ≫ a ≫ integralCurveProductChart W true false)
        (leftInfinityLift_inclusion W).symm
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := smoothCurveAddition_originalPolynomial W true false
    (f ≫ smoothProductLeftZero W)
    (g ≫ Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom)) hi
  have hout : Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 2 2).toRingHom) = 𝟙 _ :=
    projectiveAdditionChartSpec_left_identity W
  change (f ≫ smoothProductLeftZero W) ≫ smoothCurveAddition W ≫
    (integralSmoothOpen W).ι = _ at he
  change _ = (g ≫ Spec.map (CommRingCat.ofHom
    (chartProductLeftInfinityLift W).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 2 2).toRingHom) ≫
        integralCurveChart W 2 at he
  simp only [Category.assoc] at he
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom
    (chartProductLeftInfinityLift W).toRingHom)) _ (integralCurveChart W 2),
    hout, Category.id_comp] at he
  simpa only [Category.assoc, h] using he

/-- Zero on the right fixes any smooth point with an affine presentation. -/
theorem smoothCurveAddition_rightZero_affine {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (Coordinate W 2)))
    (h : f ≫ (integralSmoothOpen W).ι = g ≫ integralCurveChart W 2) :
    f ≫ smoothProductRightZero W ≫ smoothCurveAddition W = f := by
  have hi : (f ≫ smoothProductRightZero W) ≫ (smoothCurveProductOpen W).ι =
      (g ≫ Spec.map (CommRingCat.ofHom (chartProductRightInfinityLift W).toRingHom)) ≫
        projectiveAdditionInclusion W 2 1 2 ≫ integralCurveProductChart W false true := by
    rw [Category.assoc, smoothProductRightZero_inclusion, ← Category.assoc, h, Category.assoc]
    have hc : integralCurveChart W 2 ≫ integralCurveRightZero W =
        Spec.map (CommRingCat.ofHom (chartProductAtRightInfinity W 2).toRingHom) ≫
          integralCurveProductChart W false true := integralCurveChart_rightZero W false
    rw [hc]
    simpa only [Category.assoc] using
      congrArg (fun a => g ≫ a ≫ integralCurveProductChart W false true)
        (rightInfinityLift_inclusion W).symm
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := smoothCurveAddition_originalPolynomial W false true
    (f ≫ smoothProductRightZero W)
    (g ≫ Spec.map (CommRingCat.ofHom (chartProductRightInfinityLift W).toRingHom)) hi
  have hout : Spec.map (CommRingCat.ofHom (chartProductRightInfinityLift W).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 2 1 2).toRingHom) = 𝟙 _ :=
    projectiveAdditionChartSpec_right_identity W
  change _ = (g ≫ Spec.map (CommRingCat.ofHom
    (chartProductRightInfinityLift W).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 2 1 2).toRingHom) ≫
        integralCurveChart W 2 at he
  simp only [Category.assoc] at he
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom
    (chartProductRightInfinityLift W).toRingHom)) _ (integralCurveChart W 2),
    hout, Category.id_comp] at he
  simpa only [Category.assoc, h] using he

end FLT.Mazur.WeierstrassIntegralChart
