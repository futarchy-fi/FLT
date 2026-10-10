/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeAffineAgreement
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedFixedCoordinates
public import FLT.Mazur.UniversalWeierstrassAuxiliaryMarkingInvariant

/-!
# Actual normalized slice points are independent of marked affine presentations

An isomorphism of the original proper cubics preserving the zero section and
every nonidentity label identifies their actual normalized slice points.
The proved invariance of equations and coordinates supplies every comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f g : Spec (.of R) ⟶ levelFour.left)
  (e : integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≅
    integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections g)))
  (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections g)) =
    integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections f)))
  (hz : integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≫ e.hom =
    integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections g)))
  (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
    auxiliaryPullbackSection (auxiliaryPointSections f) a ha ≫ e.hom =
      auxiliaryPullbackSection (auxiliaryPointSections g) a ha)

include hb hz hm in
/-- Marked proper isomorphism identifies the entire actual normalized auxiliary point. -/
theorem auxiliaryFamilyNormalizedPoint_invariant :
    auxiliaryFamilyNormalizedPoint f = auxiliaryFamilyNormalizedPoint g := by
  apply auxiliarySchemePoint_ext_coordinates
  · rw [auxiliaryFamilyNormalizedPoint_base, auxiliaryFamilyNormalizedPoint_base]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change auxiliaryNormalizedCoefficientHom (auxiliaryPointSections f) =
      auxiliaryNormalizedCoefficientHom (auxiliaryPointSections g)
    apply parameterHom_eq_of_equation
    rw [auxiliaryNormalizedCoefficientHom_equation, auxiliaryNormalizedCoefficientHom_equation]
    exact (auxiliaryNormalization_invariant _ _ e hb hz hm).1
  · intro a ha i
    apply (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective
    change auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f) (auxiliaryCoordinate a ha i) =
      auxiliaryPointSections (auxiliaryFamilyNormalizedPoint g) (auxiliaryCoordinate a ha i)
    rw [auxiliaryFamilyNormalizedPoint_coordinate, auxiliaryFamilyNormalizedPoint_coordinate]
    exact auxiliaryNormalizedMarking_invariant _ _ e hb hz hm a ha i

include hb hz hm in
/-- The actual original closed-slice point is independent of the marked proper presentation. -/
theorem auxiliaryFamilyNormalizedSlicePoint_invariant :
    auxiliaryFamilyNormalizedSlicePoint f = auxiliaryFamilyNormalizedSlicePoint g := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [auxiliaryFamilyNormalizedSlicePoint_inclusion, auxiliaryFamilyNormalizedSlicePoint_inclusion]
  exact auxiliaryFamilyNormalizedPoint_invariant f g e hb hz hm

end FLT.Mazur.UniversalWeierstrass
