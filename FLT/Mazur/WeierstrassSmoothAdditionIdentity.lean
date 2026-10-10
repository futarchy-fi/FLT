/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothYIdentity

/-!
# Two-sided identities on the full smooth curve

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

/-- Zero is a left identity on the entire relative smooth curve. -/
@[reassoc] theorem smoothCurveAddition_left_identity :
    smoothProductLeftZero W ≫ smoothCurveAddition W = 𝟙 _ := by
  let C := integralCurveTwoChartCover W
  let i := (integralSmoothOpen W).ι
  apply Scheme.Cover.hom_ext (C.pullback₁ i)
  intro b
  let p := (C.pullback₁ i).f b
  let q := Scheme.Cover.pullbackHom C i b
  have hi : p ≫ i = q ≫ C.f b := (Scheme.Cover.pullbackHom_map C i b).symm
  change p ≫ (smoothProductLeftZero W ≫ smoothCurveAddition W) = p ≫ 𝟙 _
  rw [Category.comp_id]
  cases b
  · exact smoothCurveAddition_leftZero_affine W p q hi
  · exact smoothCurveAddition_leftZero_yChart W p q hi

/-- The categorical smooth addition has the same left identity. -/
@[reassoc] theorem smoothFactorAddition_left_identity :
    smoothFactorLeftZero W ≫ smoothFactorAddition W = 𝟙 _ := by
  rw [smoothFactorAddition, ← Category.assoc]
  exact smoothCurveAddition_left_identity W

/-- Zero is a right identity on the entire relative smooth curve. -/
@[reassoc] theorem smoothCurveAddition_right_identity :
    smoothProductRightZero W ≫ smoothCurveAddition W = 𝟙 _ := by
  let C := integralCurveTwoChartCover W
  let i := (integralSmoothOpen W).ι
  apply Scheme.Cover.hom_ext (C.pullback₁ i)
  intro b
  let p := (C.pullback₁ i).f b
  let q := Scheme.Cover.pullbackHom C i b
  have hi : p ≫ i = q ≫ C.f b := (Scheme.Cover.pullbackHom_map C i b).symm
  change p ≫ (smoothProductRightZero W ≫ smoothCurveAddition W) = p ≫ 𝟙 _
  rw [Category.comp_id]
  cases b
  · exact smoothCurveAddition_rightZero_affine W p q hi
  · exact smoothCurveAddition_rightZero_yChart W p q hi

/-- The categorical smooth addition has the same right identity. -/
@[reassoc] theorem smoothFactorAddition_right_identity :
    smoothFactorRightZero W ≫ smoothFactorAddition W = 𝟙 _ := by
  rw [smoothFactorAddition, ← Category.assoc]
  exact smoothCurveAddition_right_identity W

end FLT.Mazur.WeierstrassIntegralChart
