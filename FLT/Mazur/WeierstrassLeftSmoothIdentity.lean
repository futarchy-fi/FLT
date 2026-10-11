/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothYIdentity

/-!
# Zero acts identically on the whole integral cubic

Descent through the original Y/Z cover proves the identity as a scheme morphism,
retaining singular points, nilpotents and the original coefficient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Zero fixes every point of the whole original cubic, as a scheme morphism. -/
@[reassoc] theorem leftSmoothCurveAddition_left_identity :
    leftSmoothProductZero W ≫ leftSmoothCurveAddition W = 𝟙 _ := by
  apply Scheme.Cover.hom_ext (integralCurveTwoChartCover W)
  intro b
  rw [Category.comp_id]
  cases b
  · exact leftSmoothCurveAddition_leftZero_affine W _ (𝟙 _) (Category.id_comp _).symm
  · exact leftSmoothCurveAddition_leftZero_yChart W _ (𝟙 _) (Category.id_comp _).symm

/-- The categorical smooth by whole product law has the same identity. -/
@[reassoc] theorem leftSmoothFactorAddition_left_identity :
    leftSmoothFactorZero W ≫ leftSmoothFactorAddition W = 𝟙 _ := by
  rw [leftSmoothFactorAddition, ← Category.assoc]
  exact leftSmoothCurveAddition_left_identity W

/-- Every scheme-valued original point is fixed by the actual smooth zero section. -/
theorem leftSmoothPointAddition_zero {X : Scheme.{u}} (f : X ⟶ integralCurve W)
    (h : (f ≫ integralCurveStructure W ≫ integralSmoothZero W) ≫
      integralSmoothStructure W = f ≫ integralCurveStructure W) :
    leftSmoothPointAddition W (f ≫ integralCurveStructure W ≫ integralSmoothZero W) f h = f := by
  have hg : pullback.lift (f ≫ integralCurveStructure W ≫ integralSmoothZero W) f h =
      f ≫ leftSmoothFactorZero W := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, leftSmoothFactorZero_fst]
    · rw [pullback.lift_snd, Category.assoc, leftSmoothFactorZero_snd, Category.comp_id]
  rw [leftSmoothPointAddition, hg, Category.assoc,
    leftSmoothFactorAddition_left_identity, Category.comp_id]

end FLT.Mazur.WeierstrassIntegralChart
