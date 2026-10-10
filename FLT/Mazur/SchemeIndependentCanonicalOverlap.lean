/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentPairNormalization

/-!
# Canonical overlaps for two independent pullback paths

The two member schemes may differ. Their canonical overlap normalizes to
the canonical overlap on any further test scheme, over any common base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentCanonicalOverlap
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y₁ Y₂ Z T : Scheme.{u}}

/-- Identify pullbacks from two different members through their common base path. -/
def overlap (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
    (k : Z ⟶ X) (hl : l ≫ f = k) (hr : r ≫ g = k) (A : X.Modules) :
    (pullback l).obj ((pullback f).obj A) ≅ (pullback r).obj ((pullback g).obj A) :=
  (comparison l f k hl).app A ≪≫ ((comparison r g k hr).app A).symm

/-- Normalization retains the canonical overlap for independent member schemes. -/
lemma normalize_overlap (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
    (k : Z ⟶ X) (hl : l ≫ f = k) (hr : r ≫ g = k)
    (t : T ⟶ Z) (l' : T ⟶ Y₁) (r' : T ⟶ Y₂)
    (wl : t ≫ l = l') (wr : t ≫ r = r') (k' : T ⟶ X)
    (hl' : l' ≫ f = k') (hr' : r' ≫ g = k') (A : X.Modules) :
    SchemeIndependentPairNormalization.normalize l r t l' r' wl wr
      ((pullback f).obj A) ((pullback g).obj A) (overlap f g l r k hl hr A) =
        overlap f g l' r' k' hl' hr' A := by
  have hk : t ≫ k = k' := by rw [← hl, ← Category.assoc, wl, hl']
  have ha := comparison_assoc t l f l' k k' wl hl hk hl' A
  have hb := comparison_assoc t r g r' k k' wr hr hk hr' A
  apply Iso.ext
  apply (cancel_epi ((comparison t l l' wl).hom.app ((pullback f).obj A))).mp
  apply (cancel_mono ((comparison r' g k' hr').hom.app A)).mp
  simp only [SchemeIndependentPairNormalization.normalize, overlap,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rw [← hb]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  exact ha

end FLT.Mazur.SchemeIndependentCanonicalOverlap
