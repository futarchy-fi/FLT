/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualPullbackComposition
public import FLT.Mazur.SchemePullbackSquare

/-!
# Canonical dual pullback around a commutative square

The comparison uses the original composition and equality isomorphisms of
sheaf pullbacks, and the intrinsic contravariant dual on sheaf morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open SchemePullbackSquare SheafPullbackPathComparison
variable {P X T S : Scheme.{u}}

/-- The canonical dual comparison respects equality of scheme morphisms. -/
@[reassoc]
lemma moduleSheafDualPullbackHom_congr {f g : X ⟶ S} (w : f = g) (M : S.Modules) :
    (pullbackCongr w).hom.app (moduleSheafDual M) ≫ moduleSheafDualPullbackHom g M =
      moduleSheafDualPullbackHom f M ≫
        moduleSheafDualMap ((pullback g).obj M) ((pullbackCongr w).inv.app M) := by
  subst g
  simp [pullbackCongr]

/-- Canonical dual pullback commutes with the actual square comparison. -/
@[reassoc]
lemma moduleSheafDualPullbackHom_square
    (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (w : q ≫ g = p ≫ f) (M : S.Modules) :
    (pullback q).map (moduleSheafDualPullbackHom g M) ≫
        moduleSheafDualPullbackHom q ((pullback g).obj M) ≫
          moduleSheafDualMap ((pullback p).obj ((pullback f).obj M))
            ((squareIso f q g p w).inv.app M) =
      (squareIso f q g p w).hom.app (moduleSheafDual M) ≫
        (pullback p).map (moduleSheafDualPullbackHom f M) ≫
          moduleSheafDualPullbackHom p ((pullback f).obj M) := by
  rw [moduleSheafDualPullbackHom_comp_assoc,
    moduleSheafDualPullbackHom_comp p f M]
  simp only [squareIso, comparison, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [moduleSheafDualPullbackHom_congr_assoc]
  simp only [moduleSheafDualMap_comp, Category.assoc]
  congr 2
  rw [← Category.assoc, ← Category.assoc, ← moduleSheafDualMap_comp,
    Iso.inv_hom_id_app, moduleSheafDualMap_id, Category.id_comp]

end FLT.Mazur.FCurve
