/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison
public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# Pullback comparisons for a square of retractions

The pullback comparison around a commutative square is compatible with
retraction to the diagonal, including a change of the underlying sheaf base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackRetractionSquare
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z Y' Z' : Scheme.{u}}

/-- Normalize a retraction followed by another morphism. -/
@[reassoc]
theorem retract_comp (d : Y' ⟶ Z') (l : Z' ⟶ Y') (h : d ≫ l = 𝟙 Y')
    (b : Y' ⟶ Y) (w : d ≫ (l ≫ b) = b) (M : Y.Modules) :
    (pullback d).map ((pullbackComp l b).hom.app M) ≫
      (comparison d (l ≫ b) b w).hom.app M =
    (retractIso d l h ((pullback b).obj M)).hom := by
  have hh := comparison_assoc d l b (𝟙 Y') (l ≫ b) b h rfl w (by simp) M
  rw [comparison_id_comp] at hh
  simpa only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl,
    retractIso, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Category.assoc] using hh

/-- Normalize a morphism followed by a retraction. -/
@[reassoc]
theorem comp_retract (b : Y' ⟶ Y) (d : Y ⟶ Z) (l : Z ⟶ Y)
    (h : d ≫ l = 𝟙 Y) (w : (b ≫ d) ≫ l = b) (M : Y.Modules) :
    (pullbackComp b d).hom.app ((pullback l).obj M) ≫
      (comparison (b ≫ d) l b w).hom.app M =
    (pullback b).map (retractIso d l h M).hom := by
  have hh := comparison_assoc b d l (b ≫ d) (𝟙 Y) b rfl h (by simp) w M
  rw [comparison_comp_id] at hh
  simpa only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl,
    retractIso, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc] using hh.symm

/-- Projection and diagonal squares commute with the actual retraction comparisons. -/
theorem square_retract (l : Z ⟶ Y) (l' : Z' ⟶ Y') (b : Y' ⟶ Y) (k : Z' ⟶ Z)
    (wl : k ≫ l = l' ≫ b) (d : Y ⟶ Z) (d' : Y' ⟶ Z')
    (wd : d' ≫ k = b ≫ d) (hl : d ≫ l = 𝟙 Y) (hl' : d' ≫ l' = 𝟙 Y')
    (M : Y.Modules) :
    (pullback d').map
        (((pullbackComp l' b).app M ≪≫ ((comparison k l (l' ≫ b) wl).app M).symm).hom) ≫
      ((comparison d' k (b ≫ d) wd).hom.app ((pullback l).obj M)) ≫
      ((pullbackComp b d).inv.app ((pullback l).obj M)) ≫
      (pullback b).map (retractIso d l hl M).hom =
    (retractIso d' l' hl' ((pullback b).obj M)).hom := by
  have w₁ : d' ≫ (l' ≫ b) = b := by rw [← Category.assoc, hl', Category.id_comp]
  have w₂ : (b ≫ d) ≫ l = b := by rw [Category.assoc, hl, Category.comp_id]
  have ha := comparison_assoc d' k l (b ≫ d) (l' ≫ b) b wd wl w₁ w₂ M
  rw [← comp_retract b d l hl w₂ M]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← ha]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  exact retract_comp d' l' hl' b w₁ M

end FLT.Mazur.SheafPullbackRetractionSquare
