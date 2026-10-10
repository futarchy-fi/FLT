/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeRigidity

/-!
# Uniqueness of marked isomorphisms to an arbitrary presentation

The target need not carry Weierstrass coordinates. Comparing two actual
isomorphisms through their quotient automorphism removes the coordinate
choice from the uniqueness statement used in isomorphism descent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- Two base-preserving isomorphisms with the same origin and marked images coincide. -/
theorem auxiliary_marked_iso_unique {X : Scheme} (π : X ⟶ Spec (.of R))
    (e f : integralCurve (auxiliaryPullbackEquation g) ≅ X)
    (he : e.hom ≫ π = integralCurveStructure (auxiliaryPullbackEquation g))
    (hf : f.hom ≫ π = integralCurveStructure (auxiliaryPullbackEquation g))
    (hz : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation g) ≫ f.hom)
    (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
      auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection g a ha ≫ f.hom) :
    e = f := by
  have hb : f.inv ≫ integralCurveStructure (auxiliaryPullbackEquation g) = π := by
    rw [← hf, f.inv_hom_id_assoc]
  have hid := auxiliary_scheme_rigidity_after_pullback g (e ≪≫ f.symm)
    (by simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hb] using he)
    (by rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hz,
      Category.assoc, f.hom_inv_id, Category.comp_id])
    (fun a ha ↦ by
      rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hm a ha,
        Category.assoc, f.hom_inv_id, Category.comp_id])
  apply Iso.ext
  have hh := congrArg (fun k ↦ k ≫ f.hom) hid
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, f.inv_hom_id,
    Category.comp_id, Category.id_comp] using hh

/-- Automorphism rigidity is unchanged by replacing the cubic with an isomorphic scheme. -/
theorem auxiliary_rigidity_in_presentation {X : Scheme} (π : X ⟶ Spec (.of R))
    (e : integralCurve (auxiliaryPullbackEquation g) ≅ X)
    (he : e.hom ≫ π = integralCurveStructure (auxiliaryPullbackEquation g))
    (f : X ≅ X) (hb : f.hom ≫ π = π)
    (hz : (integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom) ≫ f.hom =
      integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom)
    (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
      (auxiliaryPullbackSection g a ha ≫ e.hom) ≫ f.hom =
        auxiliaryPullbackSection g a ha ≫ e.hom) : f.hom = 𝟙 X := by
  have h := auxiliary_marked_iso_unique g π (e ≪≫ f) e
    (by simpa only [Iso.trans_hom, Category.assoc, hb] using he) he
    (by simpa only [Iso.trans_hom, Category.assoc] using hz)
    (fun a ha ↦ by simpa only [Iso.trans_hom, Category.assoc] using hm a ha)
  have hh := congrArg Iso.hom h
  exact (cancel_epi e.hom).mp (by simpa only [Iso.trans_hom, Category.comp_id] using hh)

end FLT.Mazur.UniversalWeierstrass
