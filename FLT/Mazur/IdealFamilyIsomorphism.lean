/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedIdealCartesianDegree

/-!
# Full ideal families under an ambient isomorphism

An actual ambient isomorphism over the base transports full ideal families
by pullback along its inverse. Degree is proved by the resulting cartesian
square. Both inverse laws and compatibility with commuting ambient maps
are equalities of the complete ideal sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A B S : Scheme.{u}} (e : A ≅ B) (p : A ⟶ S) (q : B ⟶ S)
variable (h : e.hom ≫ q = p) (d : ℕ)

include h in
/-- Pullback along an ambient isomorphism preserves the actual finite locally free degree. -/
theorem idealFamilyIso_degree (J : A.IdealSheafData)
    (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫ p) d) :
    FiniteLocallyFreeDegree ((J.comap e.inv).subschemeι ≫ q) d := by
  have he : e.inv ≫ p = q := by rw [← h, e.inv_hom_id_assoc]
  exact restriction_degree J e.inv
    (IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id q).symm⟩) d hJ

/-- Transport every full ideal family across an actual ambient isomorphism over the base. -/
def idealFamilyIsoEquiv :
    { J : A.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ p) d } ≃
    { J : B.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ q) d } where
  toFun J := ⟨J.val.comap e.inv, idealFamilyIso_degree e p q h d J.val J.property⟩
  invFun J := ⟨J.val.comap e.hom, idealFamilyIso_degree e.symm q p
    (by change e.inv ≫ p = q; rw [← h, e.inv_hom_id_assoc]) d J.val J.property⟩
  left_inv J := by
    apply Subtype.ext
    simp only [← comap_comp, e.hom_inv_id, comap_id]
  right_inv J := by
    apply Subtype.ext
    simp only [← comap_comp, e.inv_hom_id, comap_id]

/-- The transported ideal is the full pullback along the inverse ambient isomorphism. -/
theorem idealFamilyIsoEquiv_ideal
    (J : { J : A.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ p) d }) :
    (idealFamilyIsoEquiv e p q h d J).val = J.val.comap e.inv := rfl

/-- Commuting ambient isomorphisms transport full pullback ideals compatibly. -/
theorem idealFamilyIso_comap {A' B' : Scheme.{u}} (e' : A' ≅ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (he : e'.hom ≫ b = a ≫ e.hom)
    (J : A.IdealSheafData) :
    (J.comap a).comap e'.inv = (J.comap e.inv).comap b := by
  rw [← comap_comp, ← comap_comp]
  apply congrArg J.comap
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, ← he, e'.inv_hom_id_assoc, Category.assoc, e.inv_hom_id,
    Category.comp_id]

end FLT.Mazur.ClosedIdealCover
