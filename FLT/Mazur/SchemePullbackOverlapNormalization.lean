/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackNormalization
public import FLT.Mazur.SchemePullbackOverlap

/-!
# Canonical pullback overlaps commute with overlap normalization

Pulling a canonical overlap along another scheme map and normalizing the
projection paths gives the canonical overlap of the new paths. This is the
overlap-map part of compatibility with a refinement square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SheafPullbackPathComparison SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z T : Scheme.{u}}

/-- Normalized pullback of a canonical overlap is the new canonical overlap. -/
theorem normalize_overlap (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
    (hl : l ≫ p = k) (hr : r ≫ p = k) (t : T ⟶ Z) (l' r' : T ⟶ Y)
    (wl : t ≫ l = l') (wr : t ≫ r = r')
    (hl' : l' ≫ p = t ≫ k) (hr' : r' ≫ p = t ≫ k) (A : X.Modules) :
    normalize l r t l' r' wl wr ((pullback p).obj A) (overlap p l r k hl hr A) =
      overlap p l' r' (t ≫ k) hl' hr' A := by
  have ha := comparison_assoc t l p l' k (t ≫ k) wl hl rfl hl' A
  have hb := comparison_assoc t r p r' k (t ≫ k) wr hr rfl hr' A
  apply Iso.ext
  apply (cancel_epi ((comparison t l l' wl).hom.app ((pullback p).obj A))).mp
  apply (cancel_mono ((comparison r' p (t ≫ k) hr').hom.app A)).mp
  simp only [SchemeOverlapDiagonalChart.normalize, overlap,
    AffineIteratedPullbackSections.compositeIso_eq_comparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rw [← hb]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  exact ha
end FLT.Mazur.SchemePullbackOverlap
