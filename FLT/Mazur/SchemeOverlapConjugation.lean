/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackOverlapNormalization

/-!
# Normalizing reconstructed canonical overlaps

Normalization commutes with changing a reconstruction chart. In particular,
the canonical overlap of a reconstructed sheaf remains canonical on a new chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SheafPullbackPathComparison SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z T : Scheme.{u}}

/-- Normalizing a reconstructed canonical overlap preserves the reconstruction chart. -/
theorem normalize_chartOverlap (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
    (hl : l ≫ p = k) (hr : r ≫ p = k) (t : T ⟶ Z) (l' r' : T ⟶ Y)
    (wl : t ≫ l = l') (wr : t ≫ r = r')
    (hl' : l' ≫ p = t ≫ k) (hr' : r' ≫ p = t ≫ k) (A : X.Modules)
    {M : Y.Modules} (e : (pullback p).obj A ≅ M) :
    normalize l r t l' r' wl wr M (chartOverlap p l r k hl hr A e) =
      chartOverlap p l' r' (t ≫ k) hl' hr' A e := by
  have hn := (comparison t l l' wl).inv.naturality e.inv
  have hm := (comparison t r r' wr).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn hm
  have hnorm := congrArg Iso.hom (normalize_overlap p l r k hl hr t l' r'
    wl wr hl' hr' A)
  apply Iso.ext
  simp only [SchemeOverlapDiagonalChart.normalize, chartOverlap, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((comparison t l l' wl).inv.app M), ← hn, Category.assoc]
  rw [hm]
  dsimp only [SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom] at hnorm
  rw [← Category.assoc ((pullback t).map (overlap p l r k hl hr A).hom),
    ← Category.assoc ((comparison t l l' wl).inv.app ((pullback p).obj A)), hnorm]

end FLT.Mazur.SchemePullbackOverlap
