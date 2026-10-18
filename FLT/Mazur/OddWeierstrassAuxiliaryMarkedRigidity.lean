/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryNormalizationRigidity

/-!
# Uniqueness and trivial stabilizers for the original marked proper cubics

The full proper comparison formula implies uniqueness before normalization.
In particular the auxiliary marking kills every origin-preserving automorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open WeierstrassIntegralChart
variable {R : Type} [CommRing R] (g k : AuxiliarySectionRing →+* R)

/-- There is at most one actual base-, origin-, and auxiliary-marking-preserving isomorphism. -/
theorem auxiliaryMarkedProperIso_unique
    (e d : integralCurve (auxiliaryPullbackEquation g) ≅
      integralCurve (auxiliaryPullbackEquation k))
    (heb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation k) =
      integralCurveStructure (auxiliaryPullbackEquation g))
    (hez : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation k))
    (hem : ∀ (a : Labels 3) (ha : a ≠ 1),
      auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection k a ha)
    (hdb : d.hom ≫ integralCurveStructure (auxiliaryPullbackEquation k) =
      integralCurveStructure (auxiliaryPullbackEquation g))
    (hdz : integralCurveZero (auxiliaryPullbackEquation g) ≫ d.hom =
      integralCurveZero (auxiliaryPullbackEquation k))
    (hdm : ∀ (a : Labels 3) (ha : a ≠ 1),
      auxiliaryPullbackSection g a ha ≫ d.hom = auxiliaryPullbackSection k a ha) : e = d := by
  have h := (auxiliaryNormalization_invariant g k e heb hez hem).1
  apply Iso.ext
  exact (auxiliaryMarkedIso_hom_formula g k e heb hez hem h).trans
    (auxiliaryMarkedIso_hom_formula g k d hdb hdz hdm h).symm

/-- Every actual automorphism fixing the original auxiliary marking and origin is the identity. -/
theorem auxiliaryMarkedProperIso_eq_refl
    (e : integralCurve (auxiliaryPullbackEquation g) ≅ integralCurve (auxiliaryPullbackEquation g))
    (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation g) =
      integralCurveStructure (auxiliaryPullbackEquation g))
    (hz : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation g))
    (hm : ∀ (a : Labels 3) (ha : a ≠ 1),
      auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection g a ha) :
    e = Iso.refl _ :=
  auxiliaryMarkedProperIso_unique g g e (Iso.refl _) hb hz hm
    (Category.id_comp _) (Category.comp_id _) (fun _ _ ↦ Category.comp_id _)

end FLT.Mazur.OddWeierstrassParameter
