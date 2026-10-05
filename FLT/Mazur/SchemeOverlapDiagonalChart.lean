/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison
public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# Diagonal equations under a change of overlap chart

An overlap chart commuting with the diagonal preserves its sheaf diagonal
identity. The proof uses the actual pullback associativity comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapDiagonalChart
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z Z' : Scheme.{u}}

/-- The diagonal equation for an overlap with two specified retractions. -/
def DiagonalCompatible (l r : Z ⟶ Y) (d : Y ⟶ Z)
    (hl : d ≫ l = 𝟙 Y) (hr : d ≫ r = 𝟙 Y) (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M) : Prop :=
  (pullback d).map e.hom ≫ (retractIso d r hr M).hom = (retractIso d l hl M).hom

/-- Normalize an overlap using the two projection comparisons of a chart. -/
def normalize (l r : Z ⟶ Y) (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r') (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M) :
    (pullback l').obj M ≅ (pullback r').obj M :=
  ((comparison k l l' wl).app M).symm ≪≫ (pullback k).mapIso e ≪≫
    (comparison k r r' wr).app M

/-- Chart normalization commutes with evaluation on the diagonal. -/
@[reassoc]
theorem comparison_retract (l : Z ⟶ Y) (k : Z' ⟶ Z) (l' : Z' ⟶ Y)
    (w : k ≫ l = l') (d : Y ⟶ Z) (d' : Y ⟶ Z') (wd : d' ≫ k = d)
    (hl : d ≫ l = 𝟙 Y) (hl' : d' ≫ l' = 𝟙 Y) (M : Y.Modules) :
    (pullback d').map ((comparison k l l' w).hom.app M) ≫
      (retractIso d' l' hl' M).hom =
    (comparison d' k d wd).hom.app ((pullback l).obj M) ≫
      (retractIso d l hl M).hom := by
  have h := comparison_assoc d' k l d l' (𝟙 Y) wd w hl' hl M
  simpa only [retractIso, comparison, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Category.assoc] using
    congrArg (fun t ↦ t ≫ (pullbackId Y).hom.app M) h

/-- Changing overlap charts preserves the actual sheaf diagonal equation. -/
theorem normalize_diagonal (l r : Z ⟶ Y) (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r')
    (d : Y ⟶ Z) (d' : Y ⟶ Z') (wd : d' ≫ k = d)
    (hl : d ≫ l = 𝟙 Y) (hr : d ≫ r = 𝟙 Y)
    (hl' : d' ≫ l' = 𝟙 Y) (hr' : d' ≫ r' = 𝟙 Y) (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M)
    (he : DiagonalCompatible l r d hl hr M e) :
    DiagonalCompatible l' r' d' hl' hr' M (normalize l r k l' r' wl wr M e) := by
  unfold DiagonalCompatible at he ⊢
  dsimp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [comparison_retract r k r' wr d d' wd hr hr' M]
  have hn := (comparison d' k d wd).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((pullback d').map ((pullback k).map e.hom)), hn]
  simp only [Category.assoc]
  rw [he, ← comparison_retract l k l' wl d d' wd hl hl' M,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end FLT.Mazur.SchemeOverlapDiagonalChart
