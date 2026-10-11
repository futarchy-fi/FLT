/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothOriginalFormulas
public import FLT.Mazur.WeierstrassLeftSmoothZeroGraph
public import FLT.Mazur.WeierstrassGlobalAdditionZeroRestrictions

/-!
# Zero fixes every affine point of the original cubic

The original polynomial identity applies without smoothness of the second input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Zero on the left fixes any point with an affine presentation. -/
theorem leftSmoothCurveAddition_leftZero_affine {X : Scheme.{u}}
    (f : X ⟶ integralCurve W)
    (g : X ⟶ Spec (.of (Coordinate W 2)))
    (h : f = g ≫ integralCurveChart W 2) :
    f ≫ leftSmoothProductZero W ≫ leftSmoothCurveAddition W = f := by
  have hi : (f ≫ leftSmoothProductZero W) ≫ (leftSmoothCurveProductOpen W).ι =
      (g ≫ Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom)) ≫
        projectiveAdditionInclusion W 1 2 2 ≫ integralCurveProductChart W true false := by
    rw [Category.assoc, leftSmoothProductZero_inclusion, h, Category.assoc]
    have hc : integralCurveChart W 2 ≫ integralCurveLeftZero W =
        Spec.map (CommRingCat.ofHom (chartProductAtLeftInfinity W 2).toRingHom) ≫
          integralCurveProductChart W true false := integralCurveChart_leftZero W false
    rw [hc]
    simpa only [Category.assoc] using
      congrArg (fun a => g ≫ a ≫ integralCurveProductChart W true false)
        (leftInfinityLift_inclusion W).symm
  have he := leftSmoothCurveAddition_originalPolynomial W true false
    (f ≫ leftSmoothProductZero W)
    (g ≫ Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom)) hi
  have hout : Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 2 2).toRingHom) = 𝟙 _ :=
    projectiveAdditionChartSpec_left_identity W
  change _ = (g ≫ Spec.map (CommRingCat.ofHom
    (chartProductLeftInfinityLift W).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 2 2).toRingHom) ≫
        integralCurveChart W 2 at he
  simp only [Category.assoc] at he
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom
    (chartProductLeftInfinityLift W).toRingHom)) _ (integralCurveChart W 2),
    hout, Category.id_comp] at he
  simpa only [Category.assoc, h] using he

end FLT.Mazur.WeierstrassIntegralChart
