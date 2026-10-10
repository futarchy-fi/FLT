/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationSmoothOpen

/-!
# The retained original smooth scheme inside the whole modification

The inverse of the full smooth-open comparison is an actual open immersion.
It retains the original structure map and is the entire contraction preimage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
open WeierstrassIntegralChart

/-- Embed the complete original relative smooth scheme in the whole modified cubic. -/
def smoothEmbedding : (integralSmoothOpen W).toScheme ⟶ model W s b3 b4 b6 h3 h4 h6 hs :=
  (smoothPreimageIso W s b3 b4 b6 h3 h4 h6 hs).inv ≫
    (contraction W s b3 b4 b6 h3 h4 h6 hs ⁻¹ᵁ integralSmoothOpen W).ι

instance smoothEmbedding_isOpenImmersion :
    IsOpenImmersion (smoothEmbedding W s b3 b4 b6 h3 h4 h6 hs) := by
  unfold smoothEmbedding
  infer_instance

/-- The retained smooth scheme contracts by its exact original inclusion. -/
@[reassoc] theorem smoothEmbedding_contraction :
    smoothEmbedding W s b3 b4 b6 h3 h4 h6 hs ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      (integralSmoothOpen W).ι := by
  rw [smoothEmbedding, Category.assoc, ← smoothPreimageIso_hom_inclusion,
    Iso.inv_hom_id_assoc]

/-- This retained smooth scheme is the full pullback of the original smooth open. -/
theorem smoothEmbedding_isPullback :
    IsPullback (𝟙 _) (smoothEmbedding W s b3 b4 b6 h3 h4 h6 hs)
      (integralSmoothOpen W).ι (contraction W s b3 b4 b6 h3 h4 h6 hs) := by
  apply (isPullback_morphismRestrict (contraction W s b3 b4 b6 h3 h4 h6 hs)
    (integralSmoothOpen W)).of_iso (smoothPreimageIso W s b3 b4 b6 h3 h4 h6 hs)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [smoothPreimageIso]
  · simp [smoothEmbedding]
  · simp
  · simp

/-- The complete inverse image has no additional points over the original smooth locus. -/
theorem smoothEmbedding_range :
    Set.range (smoothEmbedding W s b3 b4 b6 h3 h4 h6 hs) =
      contraction W s b3 b4 b6 h3 h4 h6 hs ⁻¹' (integralSmoothOpen W : Set _) := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (smoothEmbedding_isPullback W s b3 b4 b6 h3 h4 h6 hs) ⊤
  simpa using congrArg SetLike.coe h

/-- The entire retained original smooth scheme has its original structure morphism. -/
@[reassoc] theorem smoothEmbedding_structure :
    smoothEmbedding W s b3 b4 b6 h3 h4 h6 hs ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs =
      integralSmoothStructure W := by
  rw [structureMap, smoothEmbedding_contraction_assoc]

/-- The retained full smooth open is smooth over the coefficient base. -/
instance smoothEmbedding_structure_smooth :
    Smooth (smoothEmbedding W s b3 b4 b6 h3 h4 h6 hs ≫
      structureMap W s b3 b4 b6 h3 h4 h6 hs) := by
  rw [smoothEmbedding_structure]
  infer_instance

end FLT.Mazur.WeierstrassGlobalModification
