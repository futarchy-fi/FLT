/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationFixed
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizedSlice

/-!
# Normalization retracts the original auxiliary scheme onto its closed slice

The identity frame change on the slice fixes the entire actual auxiliary point.
Naturality represents normalization by one scheme morphism, with its retraction
and idempotence laws proved on the original schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T : Scheme}

/-- Normalization into the original closed slice commutes with every source morphism. -/
theorem auxiliarySchemeNormalizedSlicePoint_natural {U : Scheme}
    (f : T ⟶ levelThree.left) (k : U ⟶ T) :
    auxiliarySchemeNormalizedSlicePoint (k ≫ f) = k ≫ auxiliarySchemeNormalizedSlicePoint f := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [Category.assoc, auxiliarySchemeNormalizedSlicePoint_inclusion,
    auxiliarySchemeNormalizedSlicePoint_inclusion]
  exact auxiliarySchemeNormalizedPoint_natural f k

/-- Restriction to the original closed slice is a left inverse of scheme normalization. -/
theorem auxiliarySchemeNormalizedSlicePoint_restrict (l : T ⟶ normalizedSlice) :
    auxiliarySchemeNormalizedSlicePoint (l ≫ normalizedSliceInclusion) = l := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [auxiliarySchemeNormalizedSlicePoint_inclusion]
  exact auxiliarySchemeNormalizedPoint_fixed _ (normalizedSliceFamily_satisfies l)

/-- The actual normalization morphism from the original level-three scheme to its closed slice. -/
def auxiliaryNormalizationMorphism : levelThree.left ⟶ normalizedSlice :=
  auxiliarySchemeNormalizedSlicePoint (𝟙 levelThree.left)

/-- The normalization morphism represents the constructed normalization on every scheme family. -/
theorem auxiliaryNormalizationMorphism_comp (f : T ⟶ levelThree.left) :
    f ≫ auxiliaryNormalizationMorphism = auxiliarySchemeNormalizedSlicePoint f := by
  have h := auxiliarySchemeNormalizedSlicePoint_natural (𝟙 levelThree.left) f
  rw [Category.comp_id] at h
  exact h.symm

/-- The original slice inclusion followed by normalization is exactly the identity. -/
@[reassoc] theorem normalizedSliceInclusion_normalization :
    normalizedSliceInclusion ≫ auxiliaryNormalizationMorphism = 𝟙 normalizedSlice := by
  rw [auxiliaryNormalizationMorphism_comp]
  simpa only [Category.id_comp] using
    auxiliarySchemeNormalizedSlicePoint_restrict (𝟙 normalizedSlice)

/-- Repeating normalization fixes the original represented auxiliary point. -/
theorem auxiliarySchemeNormalizedPoint_idempotent (f : T ⟶ levelThree.left) :
    auxiliarySchemeNormalizedPoint (auxiliarySchemeNormalizedPoint f) =
      auxiliarySchemeNormalizedPoint f :=
  auxiliarySchemeNormalizedPoint_fixed _ (auxiliarySchemeNormalizedPoint_satisfies f)

end FLT.Mazur.OddWeierstrassParameter
