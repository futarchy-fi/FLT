/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedSmoothActionLaws
public import FLT.Mazur.WeierstrassLeftSmoothSectionTranslation

/-!
# Original sections translate the entire resolved smooth model

Construct actual automorphisms over the original base from the proved action
and inverse laws. Their contractions retain the original cubic translation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
variable (a : Spec (.of R) ⟶ (integralSmoothOpen W).toScheme)
  (ha : a ≫ integralSmoothStructure W = 𝟙 _)

/-- Translate every resolved smooth component by a specified original smooth section. -/
def finiteGlobalSmoothTranslation : (U).toScheme ⟶ (U).toScheme :=
  finiteGlobalSmoothPointAction hπ data j hj (t ≫ a) (𝟙 _)
    (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

/-- The constructed translation is over the unchanged original coefficients. -/
@[reassoc] theorem finiteGlobalSmoothTranslation_structure :
    finiteGlobalSmoothTranslation hπ data j hj a ha ≫ t = t := by
  rw [finiteGlobalSmoothTranslation, finiteGlobalSmoothPointAction_structure,
    Category.assoc, ha, Category.comp_id]

/-- The negative section is inverse on the full smooth locus, including exceptional components. -/
theorem finiteGlobalSmoothTranslation_neg :
    finiteGlobalSmoothTranslation hπ data j hj a ha ≫
      finiteGlobalSmoothTranslation hπ data j hj (a ≫ integralSmoothNegation W)
        (integralSmoothSection_neg_structure W a ha) = 𝟙 _ := by
  conv_lhs => arg 2; unfold finiteGlobalSmoothTranslation
  rw [← finiteGlobalSmoothPointAction_comp]
  simp only [Category.assoc, finiteGlobalSmoothTranslation_structure_assoc, Category.comp_id]
  simpa only [finiteGlobalSmoothTranslation, Category.assoc] using
    finiteGlobalSmoothPointAction_neg_cancel hπ data j hj (t ≫ a) (𝟙 _)
    (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

/-- The same negative translation cancels in the other order. -/
theorem finiteGlobalSmoothTranslation_neg_rev :
    finiteGlobalSmoothTranslation hπ data j hj (a ≫ integralSmoothNegation W)
        (integralSmoothSection_neg_structure W a ha) ≫
      finiteGlobalSmoothTranslation hπ data j hj a ha = 𝟙 _ := by
  have he := finiteGlobalSmoothTranslation_neg hπ data j hj
    (a ≫ integralSmoothNegation W) (integralSmoothSection_neg_structure W a ha)
  simpa only [Category.assoc, integralSmoothNegation_comp, Category.comp_id] using he

/-- The original smooth section gives an actual automorphism of the full resolved smooth scheme. -/
def finiteGlobalSmoothTranslationIso : (U).toScheme ≅ (U).toScheme where
  hom := finiteGlobalSmoothTranslation hπ data j hj a ha
  inv := finiteGlobalSmoothTranslation hπ data j hj (a ≫ integralSmoothNegation W)
    (integralSmoothSection_neg_structure W a ha)
  hom_inv_id := finiteGlobalSmoothTranslation_neg hπ data j hj a ha
  inv_hom_id := finiteGlobalSmoothTranslation_neg_rev hπ data j hj a ha

/-- Contraction of the automorphism is exactly translation on the original integral cubic. -/
@[reassoc] theorem finiteGlobalSmoothTranslation_contraction :
    finiteGlobalSmoothTranslation hπ data j hj a ha ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      (U).ι ≫ finiteGlobalContraction hπ data j hj ≫ integralCurveTranslation W a ha := by
  rw [finiteGlobalSmoothTranslation, finiteGlobalSmoothPointAction_contraction,
    integralCurveTranslation, ← leftSmoothPointAddition_comp]
  simp only [← leftSmoothPointAddition_comp, Category.id_comp, Category.comp_id,
    Category.assoc, finiteGlobalStructure]

end FLT.Mazur.WeierstrassDividedDepth
