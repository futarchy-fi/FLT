/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryProperNormalization

/-!
# Transport actual marked isomorphisms through proper normalization

Conjugating with the two constructed proper normalizations retains the base,
origin, and every original nonidentity marked section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

variable {R : Type} [CommRing R] (g k : AuxiliarySectionRing →+* R)
  (e : integralCurve (auxiliaryPullbackEquation g) ≅ integralCurve (auxiliaryPullbackEquation k))

/-- The induced actual isomorphism between the two canonically normalized proper cubics. -/
def auxiliaryNormalizedIso :
    integralCurve (auxiliaryNormalizedEquation g) ≅ integralCurve (auxiliaryNormalizedEquation k) :=
  auxiliaryProperNormalization g ≪≫ e ≪≫ (auxiliaryProperNormalization k).symm

/-- The conjugated isomorphism remains over the original coefficient spectrum. -/
theorem auxiliaryNormalizedIso_base
    (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation k) =
      integralCurveStructure (auxiliaryPullbackEquation g)) :
    (auxiliaryNormalizedIso g k e).hom ≫ integralCurveStructure (auxiliaryNormalizedEquation k) =
      integralCurveStructure (auxiliaryNormalizedEquation g) := by
  have hg : (auxiliaryProperNormalization g).hom ≫
      integralCurveStructure (auxiliaryPullbackEquation g) =
        integralCurveStructure (auxiliaryNormalizedEquation g) :=
    integralVariableChangeTo_structure _ _ _ rfl
  have hk : (auxiliaryProperNormalization k).hom ≫
      integralCurveStructure (auxiliaryPullbackEquation k) =
        integralCurveStructure (auxiliaryNormalizedEquation k) :=
    integralVariableChangeTo_structure _ _ _ rfl
  simp only [auxiliaryNormalizedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← hk, Iso.inv_hom_id_assoc, hb, hg]

/-- The conjugated isomorphism preserves the original zero sections. -/
theorem auxiliaryNormalizedIso_zero
    (hz : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation k)) :
    integralCurveZero (auxiliaryNormalizedEquation g) ≫ (auxiliaryNormalizedIso g k e).hom =
      integralCurveZero (auxiliaryNormalizedEquation k) := by
  apply (cancel_mono (auxiliaryProperNormalization k).hom).mp
  simp only [auxiliaryNormalizedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, auxiliaryProperNormalization_zero, hz,
    auxiliaryProperNormalization_zero]

/-- Every original normalized marking is retained by the conjugated actual isomorphism. -/
theorem auxiliaryNormalizedIso_mark (a : Labels 4) (ha : a ≠ 1)
    (hm : auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection k a ha) :
    auxiliaryNormalizedSection g a ha ≫ (auxiliaryNormalizedIso g k e).hom =
      auxiliaryNormalizedSection k a ha := by
  apply (cancel_mono (auxiliaryProperNormalization k).hom).mp
  simp only [auxiliaryNormalizedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, auxiliaryNormalizedSection_original, hm,
    auxiliaryNormalizedSection_original]

end FLT.Mazur.UniversalWeierstrass
