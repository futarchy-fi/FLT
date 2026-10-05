/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapDiagonalChart

/-!
# Detecting a diagonal equation on an overlap chart

A chart containing the diagonal detects its sheaf identity. No flatness or
faithfulness hypothesis is required: the comparison on the diagonal is an
isomorphism on the original base scheme.
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

/-- A normalized chart detects the original overlap's diagonal identity. -/
theorem diagonal_of_normalize (l r : Z ⟶ Y) (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r')
    (d : Y ⟶ Z) (d' : Y ⟶ Z') (wd : d' ≫ k = d)
    (hl : d ≫ l = 𝟙 Y) (hr : d ≫ r = 𝟙 Y)
    (hl' : d' ≫ l' = 𝟙 Y) (hr' : d' ≫ r' = 𝟙 Y) (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M)
    (he : DiagonalCompatible l' r' d' hl' hr' M (normalize l r k l' r' wl wr M e)) :
    DiagonalCompatible l r d hl hr M e := by
  unfold DiagonalCompatible at he ⊢
  have hh := congrArg
    (fun t ↦ (pullback d').map ((comparison k l l' wl).hom.app M) ≫ t) he
  dsimp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc] at hh
  simp only [Functor.map_comp, Category.assoc] at hh
  rw [comparison_retract r k r' wr d d' wd hr hr' M,
    comparison_retract l k l' wl d d' wd hl hl' M] at hh
  have hn := (comparison d' k d wd).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc] at hh
  exact (cancel_epi ((comparison d' k d wd).hom.app ((pullback l).obj M))).mp hh

/-- Normalizing on a chart containing the diagonal preserves and detects its identity. -/
theorem normalize_diagonal_iff (l r : Z ⟶ Y) (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r')
    (d : Y ⟶ Z) (d' : Y ⟶ Z') (wd : d' ≫ k = d)
    (hl : d ≫ l = 𝟙 Y) (hr : d ≫ r = 𝟙 Y)
    (hl' : d' ≫ l' = 𝟙 Y) (hr' : d' ≫ r' = 𝟙 Y) (M : Y.Modules)
    (e : (pullback l).obj M ≅ (pullback r).obj M) :
    DiagonalCompatible l' r' d' hl' hr' M (normalize l r k l' r' wl wr M e) ↔
      DiagonalCompatible l r d hl hr M e :=
  ⟨diagonal_of_normalize l r k l' r' wl wr d d' wd hl hr hl' hr' M e,
    normalize_diagonal l r k l' r' wl wr d d' wd hl hr hl' hr' M e⟩

end FLT.Mazur.SchemeOverlapDiagonalChart
