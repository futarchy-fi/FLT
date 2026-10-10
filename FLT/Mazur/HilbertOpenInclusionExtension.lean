/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenInclusionFamilies
public import FLT.Mazur.OpenIdealNestedExtension

/-!
# Hilbert inclusion classifies extension of the entire ideal

Passing from a smaller ambient open to a larger one extends the full family
ideal. The equality follows from support factorization and recovery across
nested open immersions, without assuming an isomorphism of family schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))
variable (U V : (Spec (.of (MvPolynomial I R ⧸ K))).Opens) (h : U ≤ V)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Hilbert inclusion leaves the containing-affine full family unchanged. -/
theorem openAmbientParameterInclusion_containingFamily
    (p : OpenAmbientSchemeParameters R I d K U s) :
    (ambientSchemeClassification R I d K s
      ⟨(openAmbientParameterInclusion R I d K U V h s p).val ≫
        (ambientHilbertSupportOpen R I d K V).ι,
        (Category.assoc _ _ _).trans
          (openAmbientParameterInclusion R I d K U V h s p).property⟩).val =
      (ambientSchemeClassification R I d K s
        ⟨p.val ≫ (ambientHilbertSupportOpen R I d K U).ι,
          (Category.assoc _ _ _).trans p.property⟩).val := by
  apply congrArg (fun f : AmbientSchemeParameters R I d K s ↦
    (ambientSchemeClassification R I d K s f).val)
  apply Subtype.ext
  exact openAmbientParameterInclusion_ambient R I d K U V h s p

/-- The containing-affine family is actually supported in its original relative open. -/
theorem openAmbientParameter_family_support (p : OpenAmbientSchemeParameters R I d K U s) :
    Set.range (ambientSchemeClassification R I d K s
      ⟨p.val ≫ (ambientHilbertSupportOpen R I d K U).ι,
        (Category.assoc _ _ _).trans p.property⟩).val.subschemeι ⊆
      Set.range (quotientRelativeOpen R I K U s).ι := by
  apply (quotientFamily_range_relativeOpen_iff R I d K U s _).mpr
  apply (range_subset_ambientHilbertSupportOpen_iff R I d K U s _).mp
  rintro _ ⟨x, rfl⟩
  exact (p.val x).property

/-- Enlarging the permitted ambient extends the entire classified ideal along its inclusion. -/
theorem openAmbientParameterInclusion_extension (p : OpenAmbientSchemeParameters R I d K U s) :
    (openAmbientSchemeClassification R I d K U s p).val.map
        (quotientRelativeOpenInclusion R I K U V h s) =
      (openAmbientSchemeClassification R I d K V s
        (openAmbientParameterInclusion R I d K U V h s p)).val := by
  let _ : IsOpenImmersion (quotientRelativeOpenInclusion R I K U V h s) := by
    unfold quotientRelativeOpenInclusion
    infer_instance
  rw [openAmbientSchemeClassification_ideal, openAmbientSchemeClassification_ideal,
    openAmbientParameterInclusion_containingFamily]
  have hJ := openAmbientParameter_family_support R I d K U s p
  rw [← quotientRelativeOpenInclusion_ι R I K U V h s] at hJ ⊢
  exact nestedOpenIdeal_extension _ _ _ hJ

end FLT.Mazur.HilbertChart
