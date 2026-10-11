/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingSchemeAuxiliaryMarking
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationMarking

/-!
# The arbitrary-source normalized boundary comparison retains all labels

The constructed normalization carries the actual normalized universal sections
to the original full boundary marking. Its identity label retains the original
infinity section of the boundary cubic.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  {T : Scheme} (j : T ⟶ smoothAuxiliaryOverlap t h₂ ht hf)

/-- The arbitrary-source normalized comparison retains every displayed universal label. -/
theorem smoothSchemeNormalizedGroupIso_marking (a : Labels 4) :
    auxiliarySchemeMarking
      (auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf)) a ≫
        (smoothSchemeNormalizedGroupIso t h₂ ht hf j).hom.hom.hom.hom =
          smoothOverlapMarking t h₂ ht hf j a := by
  rw [smoothSchemeNormalizedGroupIso_def]
  change _ ≫ ((auxiliarySchemeNormalizationGroupIso
    (j ≫ smoothAuxiliaryPoint t h₂ ht hf)).hom.hom.hom.hom ≫
      (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j).hom.hom.hom.hom) = _
  rw [← Category.assoc, auxiliarySchemeNormalizationGroupIso_marking,
    smoothSchemeAuxiliaryGroupIso_marking]

/-- The original overlap identity label projects to the original boundary infinity section. -/
@[reassoc] theorem smoothOverlapMarking_one_fst :
    (smoothOverlapMarking t h₂ ht hf j 1).left ≫
      pullback.fst (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) =
        (j ≫ smoothAuxiliaryProjection t h₂ ht hf) ≫ marking t := by
  rw [smoothOverlapMarking_fst, map_one]
  change (𝟙 T ≫ (j ≫ smoothAuxiliaryProjection t h₂ ht hf)) ≫ marking t = _
  rw [Category.id_comp]

/-- The actual normalized identity retains infinity on the unchanged boundary family. -/
@[reassoc] theorem smoothSchemeNormalizedGroupIso_one_fst :
    (auxiliarySchemeMarking
      (auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf)) 1).left ≫
        (smoothSchemeNormalizedGroupIso t h₂ ht hf j).hom.hom.hom.hom.left ≫
          pullback.fst (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) =
            (j ≫ smoothAuxiliaryProjection t h₂ ht hf) ≫ marking t := by
  rw [← Category.assoc, ← Over.comp_left, smoothSchemeNormalizedGroupIso_marking,
    smoothOverlapMarking_one_fst]

end FLT.Mazur.OneGonSmoothing
