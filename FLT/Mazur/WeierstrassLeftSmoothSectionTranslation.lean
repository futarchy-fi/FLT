/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# Whole-cubic translation by an actual smooth section

Every section of the original relative smooth curve gives an automorphism of
the whole original cubic over the original coefficient scheme. Its inverse
is translation by the actual negative section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (a : Spec (.of R) ⟶ (integralSmoothOpen W).toScheme)
  (ha : a ≫ integralSmoothStructure W = 𝟙 _)

/-- Translation by a specified smooth section on the whole original cubic. -/
def integralCurveTranslation : integralCurve W ⟶ integralCurve W :=
  leftSmoothPointAddition W (integralCurveStructure W ≫ a) (𝟙 _)
    (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

/-- Translation preserves the original coefficient morphism. -/
@[reassoc] theorem integralCurveTranslation_structure :
    integralCurveTranslation W a ha ≫ integralCurveStructure W = integralCurveStructure W := by
  rw [integralCurveTranslation, leftSmoothPointAddition_structure, Category.assoc, ha,
    Category.comp_id]

include ha in
/-- The negative of a smooth section is again a section over the same coefficients. -/
theorem integralSmoothSection_neg_structure :
    (a ≫ integralSmoothNegation W) ≫ integralSmoothStructure W = 𝟙 _ := by
  rw [Category.assoc, integralSmoothNegation_structure, ha]

/-- Translation by the negative section undoes the specified translation. -/
theorem integralCurveTranslation_neg :
    integralCurveTranslation W a ha ≫
      integralCurveTranslation W (a ≫ integralSmoothNegation W)
        (integralSmoothSection_neg_structure W a ha) = 𝟙 _ := by
  conv_lhs => arg 2; unfold integralCurveTranslation
  rw [← leftSmoothPointAddition_comp]
  simp only [← Category.assoc, integralCurveTranslation_structure, Category.comp_id]
  exact leftSmoothPointAddition_neg_cancel W (integralCurveStructure W ≫ a) (𝟙 _)
    (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

/-- The two section translations are inverse in the other order as well. -/
theorem integralCurveTranslation_neg_rev :
    integralCurveTranslation W (a ≫ integralSmoothNegation W)
        (integralSmoothSection_neg_structure W a ha) ≫
      integralCurveTranslation W a ha = 𝟙 _ := by
  have h := integralCurveTranslation_neg W (a ≫ integralSmoothNegation W)
    (integralSmoothSection_neg_structure W a ha)
  simpa only [Category.assoc, integralSmoothNegation_comp, Category.comp_id] using h

/-- The actual translation automorphism, including the whole singular locus. -/
def integralCurveTranslationIso : integralCurve W ≅ integralCurve W where
  hom := integralCurveTranslation W a ha
  inv := integralCurveTranslation W (a ≫ integralSmoothNegation W)
    (integralSmoothSection_neg_structure W a ha)
  hom_inv_id := integralCurveTranslation_neg W a ha
  inv_hom_id := integralCurveTranslation_neg_rev W a ha

/-- The same original translation automorphism in the category over the coefficients. -/
def integralCurveTranslationOverIso :
    Over.mk (integralCurveStructure W) ≅ Over.mk (integralCurveStructure W) where
  hom := Over.homMk (integralCurveTranslationIso W a ha).hom
    (integralCurveTranslation_structure W a ha)
  inv := Over.homMk (integralCurveTranslationIso W a ha).inv
    (integralCurveTranslation_structure W _ (integralSmoothSection_neg_structure W a ha))
  hom_inv_id := by
    apply Over.OverMorphism.ext
    exact (integralCurveTranslationIso W a ha).hom_inv_id
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact (integralCurveTranslationIso W a ha).inv_hom_id

end FLT.Mazur.WeierstrassIntegralChart
