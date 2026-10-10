/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeAffineAgreement

/-!
# Actual scheme normalization commutes with every source morphism

Coefficient naturality and every labeled coordinate identify the actual
normalized morphisms. Uniqueness transfers the equality to the closed slice.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T U : Scheme} (f : T ⟶ levelFour.left) (k : U ⟶ T)

/-- The normalized coefficient parameter commutes with every change of source scheme. -/
theorem auxiliarySchemeNormalizedPoint_natural_base :
    auxiliarySchemeNormalizedPoint (k ≫ f) ≫ levelFour.hom =
      (k ≫ auxiliarySchemeNormalizedPoint f) ≫ levelFour.hom := by
  rw [Category.assoc, auxiliarySchemeNormalizedPoint_base,
    auxiliarySchemeNormalizedPoint_base, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Category.assoc]
  apply congrArg (fun t => U.toSpecΓ ≫ t)
  change Spec.map (CommRingCat.ofHom
      (auxiliaryNormalizedCoefficientHom (k.appTop.hom.comp f.appTop.hom))) =
    Spec.map k.appTop ≫ Spec.map (CommRingCat.ofHom
      (auxiliaryNormalizedCoefficientHom f.appTop.hom))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (auxiliaryNormalizedCoefficientHom_natural f.appTop.hom k.appTop.hom).symm

/-- Normalization is natural on arbitrary schemes, including nonaffine and nonreduced tests. -/
theorem auxiliarySchemeNormalizedPoint_natural :
    auxiliarySchemeNormalizedPoint (k ≫ f) = k ≫ auxiliarySchemeNormalizedPoint f := by
  apply auxiliarySchemePoint_ext_coordinates _ _
    (auxiliarySchemeNormalizedPoint_natural_base f k)
  intro a ha i
  change (auxiliarySchemeNormalizedPoint (k ≫ f)).appTop.hom (auxiliaryCoordinate a ha i) =
    k.appTop.hom ((auxiliarySchemeNormalizedPoint f).appTop.hom (auxiliaryCoordinate a ha i))
  rw [auxiliarySchemeNormalizedPoint_coordinate, auxiliarySchemeNormalizedPoint_coordinate]
  exact auxiliaryNormalizedEvaluation_coordinate_natural f.appTop.hom k.appTop.hom a ha i

/-- The unique original closed-slice factorization is natural on all test schemes. -/
theorem auxiliarySchemeNormalizedSlicePoint_natural :
    auxiliarySchemeNormalizedSlicePoint (k ≫ f) = k ≫ auxiliarySchemeNormalizedSlicePoint f := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [Category.assoc, auxiliarySchemeNormalizedSlicePoint_inclusion,
    auxiliarySchemeNormalizedSlicePoint_inclusion, auxiliarySchemeNormalizedPoint_natural]

/-- In particular affine normalization commutes with every coefficient-ring change. -/
theorem auxiliaryFamilyNormalizedSlicePoint_natural {R S : Type} [CommRing R] [CommRing S]
    (f : Spec (.of R) ⟶ levelFour.left) (k : R →+* S) :
    auxiliaryFamilyNormalizedSlicePoint (Spec.map (CommRingCat.ofHom k) ≫ f) =
      Spec.map (CommRingCat.ofHom k) ≫ auxiliaryFamilyNormalizedSlicePoint f := by
  rw [← auxiliarySchemeNormalizedSlicePoint_eq_affine,
    auxiliarySchemeNormalizedSlicePoint_natural, auxiliarySchemeNormalizedSlicePoint_eq_affine]

end FLT.Mazur.UniversalWeierstrass
