/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackCoordinateRecovery

/-!
# Coordinate recovery preserves compatible source maps

Naturality of pullback path comparisons transports a source recovery
square to coordinates and to unnormalized pair pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackCoordinateRecovery
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Y' Z O : Scheme.{u}}

/-- A compatible source map remains compatible with coordinate recovery. -/
@[reassoc]
lemma recovery_map (l : Z ⟶ Y') (i : Y' ⟶ Y) (c : Z ⟶ Y) (w : l ≫ i = c)
    {M N : Y.Modules} {M' N' : Y'.Modules}
    (a : (pullback i).obj M ≅ M') (b : (pullback i).obj N ≅ N')
    (f : M ⟶ N) (g : M' ⟶ N')
    (h : (pullback i).map f ≫ b.hom = a.hom ≫ g) :
    (pullback c).map f ≫ (recovery l i c w N b).hom =
      (recovery l i c w M a).hom ≫ (pullback l).map g := by
  have hn := (comparison l i c w).inv.naturality f
  dsimp only [Functor.comp_map] at hn
  dsimp only [recovery, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- The unnormalized coordinate recovery also preserves a compatible source map. -/
lemma comparison_recovery_map (k : Z ⟶ O) (p : O ⟶ Y)
    (l : Z ⟶ Y') (i : Y' ⟶ Y) (c : Z ⟶ Y)
    (v : k ≫ p = c) (w : l ≫ i = c)
    {M N : Y.Modules} {M' N' : Y'.Modules}
    (a : (pullback i).obj M ≅ M') (b : (pullback i).obj N ≅ N')
    (f : M ⟶ N) (g : M' ⟶ N')
    (h : (pullback i).map f ≫ b.hom = a.hom ≫ g) :
    (pullback k).map ((pullback p).map f) ≫
        (comparison k p c v).hom.app N ≫ (recovery l i c w N b).hom =
      ((comparison k p c v).hom.app M ≫ (recovery l i c w M a).hom) ≫
        (pullback l).map g := by
  have hn := (comparison k p c v).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, recovery_map l i c w a b f g h,
    ← Category.assoc]

end FLT.Mazur.SheafPullbackCoordinateRecovery
