/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapDiagonalChart

/-!
# Compatible maps survive normalization of overlap charts

Naturality of the projection comparisons transports the geometric compatibility
square to any normalized overlap chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapDiagonalChart
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z Z' : Scheme.{u}}

/-- Normalize the actual compatibility square of two overlap isomorphisms. -/
theorem normalize_compatible (l r : Z ⟶ Y) (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r') {M N : Y.Modules}
    (e : (pullback l).obj M ≅ (pullback r).obj M)
    (e' : (pullback l).obj N ≅ (pullback r).obj N) (f : M ⟶ N)
    (hf : e.hom ≫ (pullback r).map f = (pullback l).map f ≫ e'.hom) :
    (normalize l r k l' r' wl wr M e).hom ≫ (pullback r').map f =
      (pullback l').map f ≫ (normalize l r k l' r' wl wr N e').hom := by
  have hl := (comparison k l l' wl).inv.naturality f
  have hr := (comparison k r r' wr).hom.naturality f
  dsimp only [Functor.comp_map] at hl hr
  have hc : (pullback k).map e.hom ≫ (pullback k).map ((pullback r).map f) =
      (pullback k).map ((pullback l).map f) ≫ (pullback k).map e'.hom := by
    rw [← Functor.map_comp, hf, Functor.map_comp]
  dsimp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← hr, ← Category.assoc ((pullback k).map e.hom), hc,
    Category.assoc, ← Category.assoc ((comparison k l l' wl).inv.app M), ← hl,
    Category.assoc]

end FLT.Mazur.SchemeOverlapDiagonalChart
