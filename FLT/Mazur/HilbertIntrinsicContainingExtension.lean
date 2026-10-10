/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicInclusion
public import FLT.Mazur.HilbertOpenInclusionExtension
public import FLT.Mazur.IdealIsomorphismExtension

/-!
# Full intrinsic extension into the containing affine ambient

The intrinsic family classified on a Hilbert support open extends to the
complete affine family classified by the same parameter. This identifies
full ideals in the actual containing quotient ambient, not merely their
supports or their associated reduced closed subschemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.ClosedIdealCover FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Intrinsic base change of the original open inclusion is its relative-open inclusion. -/
theorem quotientRelativeOpenIso_containing :
    (quotientRelativeOpenIso R I K U s).hom ≫
        relativeIdealAmbientHom (quotientOriginalOpenStructure R I K U)
          (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))))
          U.ι rfl s = (quotientRelativeOpen R I K U s).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeIdealAmbientHom_fst, quotientRelativeOpenIso_hom_fst]
  · rw [Category.assoc, relativeIdealAmbientHom_snd,
      quotientRelativeOpenIso_hom_snd_assoc, quotientRelativeOpenOriginalMap_ι]

/-- Extension of the entire intrinsic classified ideal recovers the containing affine family. -/
theorem openIntrinsicSchemeClassification_containingExtension
    (p : OpenAmbientSchemeParameters R I d K U s) :
    (openIntrinsicSchemeClassification R I d K U s p).val.map
        (relativeIdealAmbientHom (quotientOriginalOpenStructure R I K U)
          (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K)))) U.ι rfl s) =
      (ambientSchemeClassification R I d K s
        ⟨p.val ≫ (ambientHilbertSupportOpen R I d K U).ι,
          (Category.assoc _ _ _).trans p.property⟩).val := by
  change ((openAmbientSchemeClassification R I d K U s p).val.comap
    (quotientRelativeOpenIso R I K U s).inv).map _ = _
  rw [← idealIso_map_eq_comap, ← map_comp, quotientRelativeOpenIso_containing,
    openAmbientSchemeClassification_ideal]
  exact open_map_comap _ _ (openAmbientParameter_family_support R I d K U s p)

end FLT.Mazur.HilbertChart
