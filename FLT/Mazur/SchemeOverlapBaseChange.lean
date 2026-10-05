/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapTransportComposition

/-!
# Changing the base of coordinate pullback sheaves

An overlap between pullbacks along composite projections can be expressed
as an overlap for the pulled-back base sheaf. This change commutes with
normalized pair transport and preserves composition of isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapBaseChange
open SchemeOverlapDiagonalChart SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Y' Z T : Scheme.{u}}

/-- Express an overlap along composite projections on the pulled-back base sheaf. -/
def baseChange (l r : Z ⟶ Y') (b : Y' ⟶ Y) (M : Y.Modules)
    (e : (pullback (l ≫ b)).obj M ≅ (pullback (r ≫ b)).obj M) :
    (pullback l).obj ((pullback b).obj M) ≅ (pullback r).obj ((pullback b).obj M) :=
  (pullbackComp l b).app M ≪≫ e ≪≫ ((pullbackComp r b).app M).symm

/-- Base change of the coordinate sheaves commutes with normalized overlap transport. -/
theorem normalize_baseChange (l r : Z ⟶ Y') (b : Y' ⟶ Y) (t : T ⟶ Z)
    (c1 c2 : T ⟶ Y') (w1 : t ≫ l = c1) (w2 : t ≫ r = c2)
    (u1 : t ≫ (l ≫ b) = c1 ≫ b) (u2 : t ≫ (r ≫ b) = c2 ≫ b)
    (M : Y.Modules) (e : (pullback (l ≫ b)).obj M ≅ (pullback (r ≫ b)).obj M) :
    normalize l r t c1 c2 w1 w2 ((pullback b).obj M) (baseChange l r b M e) =
      baseChange c1 c2 b M
        (normalize (l ≫ b) (r ≫ b) t (c1 ≫ b) (c2 ≫ b) u1 u2 M e) := by
  have hl := comparison_assoc t l b c1 (l ≫ b) (c1 ≫ b) w1 rfl u1 rfl M
  have hr := comparison_assoc t r b c2 (r ≫ b) (c2 ≫ b) w2 rfl u2 rfl M
  have hcomp (f : Z ⟶ Y') : comparison f b (f ≫ b) rfl = pullbackComp f b := by
    simp [comparison, pullbackCongr]
  have hcomp' (f : T ⟶ Y') : comparison f b (f ≫ b) rfl = pullbackComp f b := by
    simp [comparison, pullbackCongr]
  rw [hcomp l, hcomp' c1] at hl
  rw [hcomp r, hcomp' c2] at hr
  apply Iso.ext
  apply (cancel_epi ((comparison t l c1 w1).hom.app ((pullback b).obj M))).mp
  apply (cancel_mono ((pullbackComp c2 b).hom.app M)).mp
  dsimp only [SchemeOverlapDiagonalChart.normalize, baseChange, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hr]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← Category.assoc ((comparison t l c1 w1).hom.app ((pullback b).obj M)), ← hl]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc, Category.comp_id]

/-- Changing the coordinate sheaf base preserves composition of three overlap maps. -/
theorem baseChange_hom_comp (c1 c2 c3 : T ⟶ Y') (b : Y' ⟶ Y) (M : Y.Modules)
    (e12 : (pullback (c1 ≫ b)).obj M ≅ (pullback (c2 ≫ b)).obj M)
    (e23 : (pullback (c2 ≫ b)).obj M ≅ (pullback (c3 ≫ b)).obj M)
    (e13 : (pullback (c1 ≫ b)).obj M ≅ (pullback (c3 ≫ b)).obj M)
    (h : e12.hom ≫ e23.hom = e13.hom) :
    (baseChange c1 c2 b M e12).hom ≫ (baseChange c2 c3 b M e23).hom =
      (baseChange c1 c3 b M e13).hom := by
  simp only [baseChange, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc e12.hom, h]

end FLT.Mazur.SchemeOverlapBaseChange
