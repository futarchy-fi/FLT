/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryMarkingInvariant
public import FLT.Mazur.WeierstrassNormalizedOriginRigidity

/-!
# Actual marked isomorphisms become equality transport after normalization

The comparison is rigid on the entire proper cubic, so it also controls any
additional sections without assuming that they lie in the nonidentity affine chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (g k : AuxiliarySectionRing →+* R)
  (e : integralCurve (auxiliaryPullbackEquation g) ≅ integralCurve (auxiliaryPullbackEquation k))
  (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation k) =
    integralCurveStructure (auxiliaryPullbackEquation g))
  (hz : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
    integralCurveZero (auxiliaryPullbackEquation k))
  (hm : ∀ (a : Labels 3) (ha : a ≠ 1),
    auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection k a ha)

include hb hz hm in
/-- The entire normalized marked comparison is the actual equation equality transport. -/
theorem auxiliaryNormalizedIso_hom_eq_transport
    (h : auxiliaryNormalizedEquation g = auxiliaryNormalizedEquation k) :
    (auxiliaryNormalizedIso g k e).hom = eqToHom (congrArg integralCurve h) :=
  normalizedOriginIso_hom_eq_transport _ _ (auxiliaryNormalizedEquation_discriminant g)
    (auxiliaryNormalizedEquation_discriminant k) (auxiliaryNormalizedIso g k e)
    (auxiliaryNormalizedIso_base g k e hb) (auxiliaryNormalizedIso_zero g k e hz)
    _ _ (auxiliaryNormalizedFrameEvaluations g) (auxiliaryNormalizedFrameEvaluations k)
    (auxiliaryNormalizedFrameEvaluations_frame g) (auxiliaryNormalizedFrameEvaluations_frame k)
    (auxiliaryNormalizedIso_frame g k e hm) h

include hb hz hm in
/-- Any additional proper section has the same normalization under the marked comparison. -/
theorem auxiliaryProperSection_normalization_invariant {T : Scheme}
    (s : T ⟶ integralCurve (auxiliaryPullbackEquation g))
    (t : T ⟶ integralCurve (auxiliaryPullbackEquation k)) (hs : s ≫ e.hom = t)
    (h : auxiliaryNormalizedEquation g = auxiliaryNormalizedEquation k) :
    (s ≫ (auxiliaryProperNormalization g).inv) ≫ eqToHom (congrArg integralCurve h) =
      t ≫ (auxiliaryProperNormalization k).inv := by
  rw [← auxiliaryNormalizedIso_hom_eq_transport g k e hb hz hm h]
  simp only [auxiliaryNormalizedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hs]

include hb hz hm in
/-- A marked proper comparison is completely determined by the two original normalizations. -/
theorem auxiliaryMarkedIso_hom_formula
    (h : auxiliaryNormalizedEquation g = auxiliaryNormalizedEquation k) :
    e.hom = (auxiliaryProperNormalization g).inv ≫
      eqToHom (congrArg integralCurve h) ≫ (auxiliaryProperNormalization k).hom := by
  rw [← auxiliaryNormalizedIso_hom_eq_transport g k e hb hz hm h]
  simp only [auxiliaryNormalizedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.OddWeierstrassParameter
