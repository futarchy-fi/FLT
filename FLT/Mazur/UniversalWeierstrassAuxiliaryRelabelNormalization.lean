/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryRelabelComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemePresentationIndependence
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationRetraction

/-!
# Normalization after relabeling is independent of the original presentation

The actual relabeled proper comparison supplies the hypotheses of marked
presentation invariance. Applying it to the constructed normalization
isomorphism proves that an intermediate normalization does not change the
final relabeled slice point, first on affine families and then on schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (e : MulAut (Labels 4))
  (f g : Spec (.of R) ⟶ levelFour.left)
  (c : integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≅
    integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections g)))
  (hb : c.hom ≫ integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections g)) =
    integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections f)))
  (hz : integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≫ c.hom =
    integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections g)))
  (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
    auxiliaryPullbackSection (auxiliaryPointSections f) a ha ≫ c.hom =
      auxiliaryPullbackSection (auxiliaryPointSections g) a ha)

include hb hz hm in
/-- Relabeling preserves presentation independence of actual normalized slice points. -/
theorem auxiliaryFamilyNormalizedSlicePoint_relabel_invariant :
    auxiliaryFamilyNormalizedSlicePoint (f ≫ (auxiliaryAction 4 e).hom) =
      auxiliaryFamilyNormalizedSlicePoint (g ≫ (auxiliaryAction 4 e).hom) :=
  auxiliaryFamilyNormalizedSlicePoint_invariant _ _ (auxiliaryRelabeledComparison e f g c)
    (auxiliaryRelabeledComparison_base e f g c hb)
    (auxiliaryRelabeledComparison_zero e f g c hz)
    (auxiliaryRelabeledComparison_mark e f g c hm)

/-- Normalizing before relabeling does not change the final actual affine slice point. -/
theorem auxiliaryFamilyNormalizedSlicePoint_relabel_normalize :
    auxiliaryFamilyNormalizedSlicePoint
      (auxiliaryFamilyNormalizedPoint f ≫ (auxiliaryAction 4 e).hom) =
        auxiliaryFamilyNormalizedSlicePoint (f ≫ (auxiliaryAction 4 e).hom) :=
  auxiliaryFamilyNormalizedSlicePoint_relabel_invariant e _ f (auxiliaryFamilyNormalizationIso f)
    (auxiliaryFamilyNormalizationIso_base f) (auxiliaryFamilyNormalizationIso_zero f)
    (auxiliaryFamilyNormalizationIso_mark f)

attribute [local irreducible] auxiliarySchemeNormalizedPoint auxiliaryFamilyNormalizedPoint
  auxiliarySchemeNormalizedSlicePoint auxiliaryFamilyNormalizedSlicePoint

/-- The same compatibility holds on arbitrary source schemes, detected on their affine cover. -/
theorem auxiliarySchemeNormalizedSlicePoint_relabel_normalize {T : Scheme}
    (f : T ⟶ levelFour.left) :
    auxiliarySchemeNormalizedSlicePoint
      (auxiliarySchemeNormalizedPoint f ≫ (auxiliaryAction 4 e).hom) =
        auxiliarySchemeNormalizedSlicePoint (f ≫ (auxiliaryAction 4 e).hom) := by
  apply T.affineCover.hom_ext
  intro i
  apply (cancel_epi (T.affineCover.X i).isoSpec.inv).mp
  let k := (T.affineCover.X i).isoSpec.inv ≫ T.affineCover.f i
  have h := auxiliaryFamilyNormalizedSlicePoint_relabel_normalize e (k ≫ f)
  rw [← auxiliarySchemeNormalizedPoint_eq_affine,
    ← auxiliarySchemeNormalizedSlicePoint_eq_affine,
    ← auxiliarySchemeNormalizedSlicePoint_eq_affine,
    auxiliarySchemeNormalizedPoint_natural] at h
  simp only [Category.assoc] at h ⊢
  rw [auxiliarySchemeNormalizedSlicePoint_natural
    (auxiliarySchemeNormalizedPoint f ≫ (auxiliaryAction 4 e).hom) k,
    auxiliarySchemeNormalizedSlicePoint_natural (f ≫ (auxiliaryAction 4 e).hom) k] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

/-- Scheme normalization absorbs an intermediate normalization before any relabeling. -/
theorem auxiliaryNormalizationMorphism_relabel (e : MulAut (Labels 4)) :
    auxiliaryNormalizationMorphism ≫ normalizedSliceInclusion ≫
      (auxiliaryAction 4 e).hom ≫ auxiliaryNormalizationMorphism =
        (auxiliaryAction 4 e).hom ≫ auxiliaryNormalizationMorphism := by
  have h := auxiliarySchemeNormalizedSlicePoint_relabel_normalize e (𝟙 levelFour.left)
  rw [← auxiliarySchemeNormalizedSlicePoint_inclusion] at h
  simpa only [← auxiliaryNormalizationMorphism_comp, Category.id_comp, Category.assoc] using h

end FLT.Mazur.UniversalWeierstrass
