/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedPresentationIndependence
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationNaturality

/-!
# Affine-local marked presentations give the same global normalized slice point

The original schemes and their actual morphisms remain present. Affine tests
carry isomorphisms of proper cubics preserving zero and every marked section;
normalization naturality descends their proved equality to the source scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Marked proper comparison on every affine test identifies the global normalized slice point. -/
theorem auxiliarySchemeNormalizedSlicePoint_invariant_of_affine_tests
    {T : Scheme} (f g : T ⟶ levelFour.left)
    (h : ∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
      let a := auxiliaryPointSections (k ≫ f)
      let b := auxiliaryPointSections (k ≫ g)
      ∃ e : integralCurve (auxiliaryPullbackEquation a) ≅
          integralCurve (auxiliaryPullbackEquation b),
        (e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation b) =
          integralCurveStructure (auxiliaryPullbackEquation a)) ∧
        (integralCurveZero (auxiliaryPullbackEquation a) ≫ e.hom =
          integralCurveZero (auxiliaryPullbackEquation b)) ∧
        (∀ (c : Labels 4) (hc : c ≠ 1),
          auxiliaryPullbackSection a c hc ≫ e.hom = auxiliaryPullbackSection b c hc)) :
    auxiliarySchemeNormalizedSlicePoint f = auxiliarySchemeNormalizedSlicePoint g := by
  apply T.affineCover.hom_ext
  intro i
  apply (cancel_epi (T.affineCover.X i).isoSpec.inv).mp
  let k := (T.affineCover.X i).isoSpec.inv ≫ T.affineCover.f i
  obtain ⟨e, hb, hz, hm⟩ := h Γ(T.affineCover.X i, ⊤) k
  have he := auxiliaryFamilyNormalizedSlicePoint_invariant (k ≫ f) (k ≫ g) e hb hz hm
  rw [← auxiliarySchemeNormalizedSlicePoint_eq_affine,
    ← auxiliarySchemeNormalizedSlicePoint_eq_affine,
    auxiliarySchemeNormalizedSlicePoint_natural,
    auxiliarySchemeNormalizedSlicePoint_natural] at he
  exact (Category.assoc _ _ _).symm.trans (he.trans (Category.assoc _ _ _))

end FLT.Mazur.UniversalWeierstrass
