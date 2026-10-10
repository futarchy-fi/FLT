/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentPairNormalization

/-!
# Coordinate recovery through independent source modules

A source recovery isomorphism induces recoveries along every coordinate.
These recoveries commute with normalized further pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackCoordinateRecovery
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Y' Z T : Scheme.{u}}

/-- Recover an independent source module along a named composite coordinate. -/
def recovery (l : Z ⟶ Y') (i : Y' ⟶ Y) (c : Z ⟶ Y) (w : l ≫ i = c)
    (M : Y.Modules) {N : Y'.Modules} (a : (pullback i).obj M ≅ N) :
    (pullback c).obj M ≅ (pullback l).obj N :=
  ((comparison l i c w).app M).symm ≪≫ (pullback l).mapIso a

/-- The same coordinate recovery is obtained before or after further normalization. -/
@[reassoc]
lemma recovery_pullback (l : Z ⟶ Y') (i : Y' ⟶ Y) (c : Z ⟶ Y)
    (w : l ≫ i = c) (t : T ⟶ Z) (d : T ⟶ Y') (z : T ⟶ Y)
    (v : t ≫ l = d) (u : t ≫ c = z) (w' : d ≫ i = z)
    (M : Y.Modules) {N : Y'.Modules} (a : (pullback i).obj M ≅ N) :
    (pullback t).map (recovery l i c w M a).hom ≫
        (comparison t l d v).hom.app N =
      (comparison t c z u).hom.app M ≫ (recovery d i z w' M a).hom := by
  have h := comparison_assoc t l i d c z v w u w' M
  have hn := (comparison t l d v).hom.naturality a.hom
  dsimp only [Functor.comp_map] at hn
  apply (cancel_epi ((pullback t).map ((comparison l i c w).hom.app M))).mp
  dsimp only [recovery, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [hn, ← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SheafPullbackCoordinateRecovery
