/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenInclusionFamilies
public import FLT.Mazur.HilbertOpenIntrinsicClassification
public import FLT.Mazur.RelativeIdealAmbientHom

/-!
# Intrinsic full-ideal compatibility for Hilbert open inclusions

The actual relative-open inclusions agree with base change of original
ambient inclusions. Consequently inclusion of Hilbert support opens
classifies full intrinsic ideals compatible with actual ambient restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (K : Ideal (MvPolynomial I R))
variable (U V : (Spec (.of (MvPolynomial I R ⧸ K))).Opens) (h : U ≤ V)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Inclusion of original ambient opens preserves the coefficient-base structure. -/
theorem quotientOriginalOpenInclusion_over :
    (Spec (.of (MvPolynomial I R ⧸ K))).homOfLE h ≫
        quotientOriginalOpenStructure R I K V = quotientOriginalOpenStructure R I K U :=
  Scheme.homOfLE_ι_assoc _ _ _

/-- The relative-open inclusion preserves its actual projection to the original open. -/
theorem quotientRelativeOpenInclusion_original :
    quotientRelativeOpenInclusion R I K U V h s ≫ quotientRelativeOpenOriginalMap R I K V s =
      quotientRelativeOpenOriginalMap R I K U s ≫
        (Spec (.of (MvPolynomial I R ⧸ K))).homOfLE h := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, quotientRelativeOpenOriginalMap_ι,
    quotientRelativeOpenInclusion_ι_assoc, Category.assoc, Scheme.homOfLE_ι,
    quotientRelativeOpenOriginalMap_ι]

/-- Relative-open inclusion is the actual base change of original ambient inclusion. -/
theorem quotientRelativeOpenIso_inclusion :
    (quotientRelativeOpenIso R I K U s).hom ≫
        relativeIdealAmbientHom (quotientOriginalOpenStructure R I K U)
          (quotientOriginalOpenStructure R I K V)
          ((Spec (.of (MvPolynomial I R ⧸ K))).homOfLE h)
          (quotientOriginalOpenInclusion_over R I K U V h) s =
      quotientRelativeOpenInclusion R I K U V h s ≫ (quotientRelativeOpenIso R I K V s).hom := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, relativeIdealAmbientHom_fst, relativeIdealAmbientHom_snd,
      quotientRelativeOpenIso_hom_fst, quotientRelativeOpenIso_hom_snd,
      quotientRelativeOpenInclusion_ι_assoc, quotientRelativeOpenIso_hom_snd_assoc,
      quotientRelativeOpenInclusion_original]

/-- Hilbert inclusion restricts to the same complete ideal on the intrinsic smaller ambient. -/
theorem openIntrinsicParameterInclusion_family (d : ℕ)
    (p : OpenAmbientSchemeParameters R I d K U s) :
    (openIntrinsicSchemeClassification R I d K V s
        (openAmbientParameterInclusion R I d K U V h s p)).val.comap
          (relativeIdealAmbientHom (quotientOriginalOpenStructure R I K U)
            (quotientOriginalOpenStructure R I K V)
            ((Spec (.of (MvPolynomial I R ⧸ K))).homOfLE h)
            (quotientOriginalOpenInclusion_over R I K U V h) s) =
      (openIntrinsicSchemeClassification R I d K U s p).val := by
  have he : relativeIdealAmbientHom (quotientOriginalOpenStructure R I K U)
      (quotientOriginalOpenStructure R I K V)
      ((Spec (.of (MvPolynomial I R ⧸ K))).homOfLE h)
      (quotientOriginalOpenInclusion_over R I K U V h) s ≫
        (quotientRelativeOpenIso R I K V s).inv =
      (quotientRelativeOpenIso R I K U s).inv ≫ quotientRelativeOpenInclusion R I K U V h s := by
    apply (cancel_epi (quotientRelativeOpenIso R I K U s).hom).mp
    rw [← Category.assoc, quotientRelativeOpenIso_inclusion, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change ((openAmbientSchemeClassification R I d K V s
    (openAmbientParameterInclusion R I d K U V h s p)).val.comap
      (quotientRelativeOpenIso R I K V s).inv).comap _ =
    (openAmbientSchemeClassification R I d K U s p).val.comap
      (quotientRelativeOpenIso R I K U s).inv
  rw [← comap_comp, he, comap_comp, openAmbientParameterInclusion_family]

end FLT.Mazur.HilbertChart
