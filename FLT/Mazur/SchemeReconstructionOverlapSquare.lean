/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackOverlapSquare

/-!
# Reconstruction overlaps across a commutative square

The square comparison transports a reconstruction chart and its canonical
overlap together. This includes arbitrary reconstructed sheaves on the cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SchemeOverlapBaseChange SchemePullbackSquare
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' T : Scheme.{u}}

/-- Changing the chart of a canonical overlap composes the chart isomorphisms. -/
theorem chartOverlap_trans (p : Y ⟶ X) (l r : T ⟶ Y) (k : T ⟶ X)
    (hl : l ≫ p = k) (hr : r ≫ p = k) (A : X.Modules)
    {M N : Y.Modules} (e : (pullback p).obj A ≅ M) (f : M ≅ N) :
    chartOverlap p l r k hl hr A (e ≪≫ f) =
      ((pullback l).mapIso f).symm ≪≫ chartOverlap p l r k hl hr A e ≪≫
        (pullback r).mapIso f := by
  apply Iso.ext
  simp only [chartOverlap, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]

/-- Base change transports the full reconstruction chart through the square. -/
theorem baseChange_chartOverlap_square (p : Y ⟶ X) (q : Y' ⟶ X')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : q ≫ a = b ≫ p)
    (l r : T ⟶ Y') (k : T ⟶ X') (hl : l ≫ q = k) (hr : r ≫ q = k)
    (hlb : (l ≫ b) ≫ p = k ≫ a) (hrb : (r ≫ b) ≫ p = k ≫ a)
    (A : X.Modules) {M : Y.Modules} (e : (pullback p).obj A ≅ M) :
    baseChange l r b M (chartOverlap p (l ≫ b) (r ≫ b) (k ≫ a) hlb hrb A e) =
      chartOverlap q l r k hl hr ((pullback a).obj A)
        ((squareIso p q a b w).app A ≪≫ (pullback b).mapIso e) := by
  rw [chartOverlap_trans, ← baseChange_overlap_square p q a b w l r k hl hr hlb hrb A]
  have hn := (pullbackComp l b).hom.naturality e.inv
  have hm := (pullbackComp r b).inv.naturality e.hom
  dsimp only [Functor.comp_map] at hn hm
  apply Iso.ext
  simp only [baseChange, chartOverlap, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Category.assoc ((pullbackComp l b).hom.app M), ← hn, Category.assoc, hm]

end FLT.Mazur.SchemePullbackOverlap
