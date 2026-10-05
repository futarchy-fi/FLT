/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapBaseChange
public import FLT.Mazur.SchemePullbackOverlapNormalization
public import FLT.Mazur.SchemePullbackSquare

/-!
# Canonical overlaps across a commutative square

Changing the base sheaf of a canonical overlap agrees with the canonical overlap
transported through the square's reconstruction isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SheafPullbackPathComparison SchemeOverlapBaseChange SchemePullbackSquare
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' T : Scheme.{u}}

/-- The square reconstruction identifies the two canonical overlaps. -/
theorem baseChange_overlap_square (p : Y ⟶ X) (q : Y' ⟶ X')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : q ≫ a = b ≫ p)
    (l r : T ⟶ Y') (k : T ⟶ X') (hl : l ≫ q = k) (hr : r ≫ q = k)
    (hlb : (l ≫ b) ≫ p = k ≫ a) (hrb : (r ≫ b) ≫ p = k ≫ a)
    (A : X.Modules) :
    baseChange l r b ((pullback p).obj A)
        (overlap p (l ≫ b) (r ≫ b) (k ≫ a) hlb hrb A) =
      chartOverlap q l r k hl hr ((pullback a).obj A)
        ((squareIso p q a b w).app A) := by
  have ha := comparison_square p q a b w l k hl hlb A
  have hb := comparison_square p q a b w r k hr hrb A
  apply Iso.ext
  apply (cancel_epi ((pullback l).map ((squareIso p q a b w).hom.app A))).mp
  apply (cancel_mono ((pullbackComp r b).hom.app ((pullback p).obj A) ≫
    (comparison (r ≫ b) p (k ≫ a) hrb).hom.app A)).mp
  simp only [baseChange, chartOverlap, overlap,
    AffineIteratedPullbackSections.compositeIso_eq_comparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  rw [hb]
  simp only [Iso.inv_hom_id_app_assoc]
  exact ha

end FLT.Mazur.SchemePullbackOverlap
