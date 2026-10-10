/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationNaturality
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedFixedCoordinates

/-!
# Normalization retracts the original auxiliary scheme onto its closed slice

The identity frame change on the slice fixes the entire actual auxiliary point.
Naturality represents normalization by one scheme morphism, with its retraction
and idempotence laws proved on the original schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T : Scheme}

/-- Normalization fixes the whole original scheme family whenever its frame is normalized. -/
theorem auxiliarySchemeNormalizedPoint_fixed (f : T ⟶ levelFour.left)
    (hn : SatisfiesNormalization f.appTop.hom) : auxiliarySchemeNormalizedPoint f = f := by
  apply auxiliarySchemePoint_ext_coordinates
  · rw [auxiliarySchemeNormalizedPoint_base]
    change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (auxiliaryNormalizedCoefficientHom f.appTop.hom)) = _
    rw [auxiliaryNormalizedCoefficientHom_fixed f.appTop.hom hn]
    exact auxiliarySchemeSections_base f
  · intro a ha i
    rw [auxiliarySchemeNormalizedPoint_coordinate]
    exact auxiliaryNormalizedEvaluation_coordinate_fixed f.appTop.hom hn a ha i

/-- Restriction to the original closed slice is a left inverse of scheme normalization. -/
theorem auxiliarySchemeNormalizedSlicePoint_restrict (l : T ⟶ normalizedSlice) :
    auxiliarySchemeNormalizedSlicePoint (l ≫ normalizedSliceInclusion) = l := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [auxiliarySchemeNormalizedSlicePoint_inclusion]
  exact auxiliarySchemeNormalizedPoint_fixed _ (normalizedSliceFamily_satisfies l)

/-- The actual normalization morphism from the original level-four scheme to its closed slice. -/
def auxiliaryNormalizationMorphism : levelFour.left ⟶ normalizedSlice :=
  auxiliarySchemeNormalizedSlicePoint (𝟙 levelFour.left)

/-- The normalization morphism represents the constructed normalization on every scheme family. -/
theorem auxiliaryNormalizationMorphism_comp (f : T ⟶ levelFour.left) :
    f ≫ auxiliaryNormalizationMorphism = auxiliarySchemeNormalizedSlicePoint f := by
  have h := auxiliarySchemeNormalizedSlicePoint_natural (𝟙 levelFour.left) f
  rw [Category.comp_id] at h
  exact h.symm

/-- The original slice inclusion followed by normalization is exactly the identity. -/
@[reassoc] theorem normalizedSliceInclusion_normalization :
    normalizedSliceInclusion ≫ auxiliaryNormalizationMorphism = 𝟙 normalizedSlice := by
  rw [auxiliaryNormalizationMorphism_comp]
  simpa only [Category.id_comp] using
    auxiliarySchemeNormalizedSlicePoint_restrict (𝟙 normalizedSlice)

/-- Repeating normalization fixes the original represented auxiliary point. -/
theorem auxiliarySchemeNormalizedPoint_idempotent (f : T ⟶ levelFour.left) :
    auxiliarySchemeNormalizedPoint (auxiliarySchemeNormalizedPoint f) =
      auxiliarySchemeNormalizedPoint f :=
  auxiliarySchemeNormalizedPoint_fixed _ (auxiliarySchemeNormalizedPoint_satisfies f)

end FLT.Mazur.UniversalWeierstrass
