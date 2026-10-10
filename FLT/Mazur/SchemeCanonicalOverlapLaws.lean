/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackOverlapNormalization

/-!
# Identity and composition laws for canonical pullback overlaps

Canonical overlaps depend only on the two paths, not the name of their common
composite. Normalized overlaps can therefore be compared over one common base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z T : Scheme.{u}} (p : Y ⟶ X)

/-- Renaming the common composite does not change the canonical overlap. -/
lemma overlap_base_eq (l r : Z ⟶ Y) (k k' : Z ⟶ X)
    (hl : l ≫ p = k) (hr : r ≫ p = k)
    (hl' : l ≫ p = k') (hr' : r ≫ p = k') (A : X.Modules) :
    overlap p l r k hl hr A = overlap p l r k' hl' hr' A := by
  have h : k = k' := hl.symm.trans hl'
  cases h
  rfl

/-- The canonical overlap along a repeated path is the identity. -/
lemma overlap_self (l : Z ⟶ Y) (k : Z ⟶ X) (h : l ≫ p = k) (A : X.Modules) :
    overlap p l l k h h A = Iso.refl _ := by
  apply Iso.ext
  exact (AffineIteratedPullbackSections.compositeIso l p k h A).hom_inv_id

/-- Canonical overlaps compose by cancelling their common middle path. -/
lemma overlap_trans (l m r : Z ⟶ Y) (k : Z ⟶ X)
    (hl : l ≫ p = k) (hm : m ≫ p = k) (hr : r ≫ p = k) (A : X.Modules) :
    (overlap p l m k hl hm A).hom ≫ (overlap p m r k hm hr A).hom =
      (overlap p l r k hl hr A).hom := by
  simp only [overlap, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- Normalization can use any chosen name for the new common base map. -/
lemma normalize_overlap_base (l r : Z ⟶ Y) (k : Z ⟶ X)
    (hl : l ≫ p = k) (hr : r ≫ p = k) (t : T ⟶ Z) (l' r' : T ⟶ Y)
    (wl : t ≫ l = l') (wr : t ≫ r = r') (k' : T ⟶ X)
    (hl' : l' ≫ p = k') (hr' : r' ≫ p = k') (A : X.Modules) :
    normalize l r t l' r' wl wr ((pullback p).obj A) (overlap p l r k hl hr A) =
      overlap p l' r' k' hl' hr' A := by
  have hlt : l' ≫ p = t ≫ k := by rw [← wl, Category.assoc, hl]
  have hrt : r' ≫ p = t ≫ k := by rw [← wr, Category.assoc, hr]
  rw [normalize_overlap p l r k hl hr t l' r' wl wr hlt hrt]
  exact overlap_base_eq p l' r' _ _ hlt hrt hl' hr' A

end FLT.Mazur.SchemePullbackOverlap
