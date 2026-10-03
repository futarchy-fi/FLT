/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineStandardComparison

/-!
# The intersection of the two projective-line charts

Transport the cartesian standard chart square along the existing Proj
comparison. The Laurent chart is consequently the full intersection of
the two open images, and the images cover the projective line.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLine
variable (K : Type u) [Field K]
/-- The original two-chart construction has the specified cartesian overlap. -/
lemma overlap_isPullback : IsPullback (overlapLeft K) (overlapRight K) (left K) (right K) := by
  apply (ProjectiveLineStandardOverlap.isPullback K).of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (standardIso K).symm
  · simp
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [← left_standardIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [← right_standardIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
/-- The Laurent overlap image is the entire intersection of chart images. -/
lemma overlap_image : (overlapLeft K ≫ left K) ''ᵁ ⊤ = left K ''ᵁ ⊤ ⊓ right K ''ᵁ ⊤ := by
  let e := (overlap_isPullback K).isoPullback
  have he : e.hom ≫ pullback.fst (left K) (right K) = overlapLeft K :=
    (overlap_isPullback K).isoPullback_hom_fst
  have hi : (overlapLeft K ≫ left K) ''ᵁ ⊤ =
      (pullback.fst (left K) (right K) ≫ left K) ''ᵁ ⊤ := by
    simp only [← he, Category.assoc, Scheme.Hom.comp_image,
      Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  rw [hi]
  ext x
  simp only [Scheme.Hom.image_top_eq_opensRange]
  exact Set.ext_iff.mp (IsOpenImmersion.range_pullback_to_base_of_left (left K) (right K)) x
/-- The two chart images cover the projective line. -/
lemma chart_images_cover : left K ''ᵁ ⊤ ⊔ right K ''ᵁ ⊤ = ⊤ := by
  ext x
  simp only [Scheme.Hom.image_top_eq_opensRange]
  change (x ∈ Set.range (left K) ∨ x ∈ Set.range (right K)) ↔ True
  exact iff_true_intro (charts_cover K x)
end FLT.Mazur.ProjectiveLine
