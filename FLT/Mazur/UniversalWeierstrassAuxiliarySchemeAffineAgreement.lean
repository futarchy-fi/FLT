/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizedSlice
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedSlicePoint
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedEvaluationNaturality
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateExt

/-!
# Scheme normalization agrees with the original affine normalization

Equality of the actual coefficient maps and every original labeled coordinate
identifies the represented auxiliary points and their unique closed-slice lifts.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

/-- The scheme and affine normalized constructions have the same actual coefficient map. -/
theorem auxiliarySchemeNormalizedPoint_affine_base :
    auxiliarySchemeNormalizedPoint f ≫ levelFour.hom =
      auxiliaryFamilyNormalizedPoint f ≫ levelFour.hom := by
  rw [auxiliarySchemeNormalizedPoint_base, auxiliaryFamilyNormalizedPoint_base,
    ← SpecMap_ΓSpecIso_hom]
  change Spec.map (Scheme.ΓSpecIso (.of R)).hom ≫
    Spec.map (CommRingCat.ofHom (auxiliaryNormalizedCoefficientHom f.appTop.hom)) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact auxiliaryNormalizedCoefficientHom_natural f.appTop.hom
    (Scheme.ΓSpecIso (.of R)).hom.hom

/-- On affine sources scheme normalization is the original actual affine normalization. -/
theorem auxiliarySchemeNormalizedPoint_eq_affine :
    auxiliarySchemeNormalizedPoint f = auxiliaryFamilyNormalizedPoint f := by
  apply auxiliarySchemePoint_ext_coordinates _ _
    (auxiliarySchemeNormalizedPoint_affine_base f)
  intro a ha i
  apply (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (.of R)).hom.hom
      ((auxiliarySchemeNormalizedPoint f).appTop.hom (auxiliaryCoordinate a ha i)) =
    auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f) (auxiliaryCoordinate a ha i)
  rw [auxiliarySchemeNormalizedPoint_coordinate, auxiliaryFamilyNormalizedPoint_coordinate]
  exact (auxiliaryNormalizedEvaluation_coordinate_natural f.appTop.hom
    (Scheme.ΓSpecIso (.of R)).hom.hom a ha i).symm

/-- The actual closed-slice points agree on every affine source, including nonreduced ones. -/
theorem auxiliarySchemeNormalizedSlicePoint_eq_affine :
    auxiliarySchemeNormalizedSlicePoint f = auxiliaryFamilyNormalizedSlicePoint f := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [auxiliarySchemeNormalizedSlicePoint_inclusion,
    auxiliaryFamilyNormalizedSlicePoint_inclusion, auxiliarySchemeNormalizedPoint_eq_affine]

end FLT.Mazur.UniversalWeierstrass
