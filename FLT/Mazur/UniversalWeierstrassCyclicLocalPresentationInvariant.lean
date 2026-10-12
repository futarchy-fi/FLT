/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicProperPresentationInvariant

/-!
# Affine-local proper comparisons identify the global full normalization

The local comparison data consist of actual proper isomorphisms retaining zero,
the auxiliary marking, and every full cyclic value. Equality of normalized
parameters is proved from these data and descended to the original source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n]

/-- Actual proper presentation comparisons preserving the original complete marking. -/
def CyclicProperPresentationRelated {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left) : Prop :=
  let a := (cyclicSchemeAuxiliaryPoint n f).appTop.hom
  let b := (cyclicSchemeAuxiliaryPoint n g).appTop.hom
  ∃ e : integralCurve (auxiliaryPullbackEquation a) ≅
      integralCurve (auxiliaryPullbackEquation b),
    (e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation b) =
      integralCurveStructure (auxiliaryPullbackEquation a)) ∧
    (integralCurveZero (auxiliaryPullbackEquation a) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation b)) ∧
    (∀ (c : Labels 4) (hc : c ≠ 1),
      auxiliaryPullbackSection a c hc ≫ e.hom = auxiliaryPullbackSection b c hc) ∧
    (∀ c : CyclicLabels n,
      cyclicSchemeOriginalCubicValue n f c ≫ e.hom = cyclicSchemeOriginalCubicValue n g c)

/-- The actual proper comparison data imply equality of full normalized parameters. -/
theorem CyclicProperPresentationRelated.normalized_eq {T : Scheme}
    {f g : T ⟶ (cyclicAuxiliaryScheme n).left} (h : CyclicProperPresentationRelated n f g) :
    cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g := by
  obtain ⟨e, hb, hz, hm, hv⟩ := h
  exact cyclicSchemeNormalizedPoint_invariant_of_proper_comparison n f g e hb hz hm hv

/-- Affine-local original proper comparisons identify the full global normalized parameter. -/
theorem cyclicSchemeNormalizedPoint_invariant_of_affine_tests {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
    (h : ∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
      CyclicProperPresentationRelated n (k ≫ f) (k ≫ g)) :
    cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g := by
  apply T.affineCover.hom_ext
  intro i
  apply (cancel_epi (T.affineCover.X i).isoSpec.inv).mp
  let k := (T.affineCover.X i).isoSpec.inv ≫ T.affineCover.f i
  have he := (h Γ(T.affineCover.X i, ⊤) k).normalized_eq n
  rw [cyclicSchemeNormalizedPoint_natural, cyclicSchemeNormalizedPoint_natural] at he
  exact (Category.assoc _ _ _).symm.trans (he.trans (Category.assoc _ _ _))

/-- Affine-local marked comparisons give a unique pair in the represented full relation. -/
def cyclicNormalizationRelationPointOfAffineTests {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
    (h : ∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
      CyclicProperPresentationRelated n (k ≫ f) (k ≫ g)) :
    T ⟶ cyclicNormalizationRelation n :=
  cyclicNormalizationRelationPoint n f g (by
    simpa only [cyclicSchemeNormalizedSlicePoint_eq_natural,
      cyclicNaturalNormalizedSlicePoint] using
      (cyclicNormalizationRelation_iff n f g).mpr
        (cyclicSchemeNormalizedPoint_invariant_of_affine_tests n f g h))

end FLT.Mazur.UniversalWeierstrass
