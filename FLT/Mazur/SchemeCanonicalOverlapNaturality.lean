/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackOverlapNormalization

/-!
# Naturality of canonical reconstruction overlaps

Maps of base sheaves commute with canonical overlaps. A map satisfying the
reconstruction square therefore intertwines the reconstructed overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
variable (hl : l ≫ p = k) (hr : r ≫ p = k)
variable {A B : X.Modules}

/-- Canonical overlaps commute with pullbacks of maps of base sheaves. -/
@[reassoc]
theorem overlap_naturality (g : A ⟶ B) :
    (overlap p l r k hl hr A).hom ≫ (pullback r).map ((pullback p).map g) =
      (pullback l).map ((pullback p).map g) ≫ (overlap p l r k hl hr B).hom := by
  have hn := (comparison r p k hr).inv.naturality g
  have hm := (comparison l p k hl).hom.naturality g
  dsimp only [Functor.comp_map] at hn hm
  simp only [overlap, AffineIteratedPullbackSections.compositeIso_eq_comparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← hn, ← Category.assoc, ← hm, Category.assoc]

/-- Every reconstruction square induces the square between canonical overlaps. -/
theorem chartOverlap_compatible {M N : Y.Modules}
    (e : (pullback p).obj A ≅ M) (e' : (pullback p).obj B ≅ N)
    (g : A ⟶ B) (f : M ⟶ N)
    (h : (pullback p).map g ≫ e'.hom = e.hom ≫ f) :
    (chartOverlap p l r k hl hr A e).hom ≫ (pullback r).map f =
      (pullback l).map f ≫ (chartOverlap p l r k hl hr B e').hom := by
  have hi : e.inv ≫ (pullback p).map g = f ≫ e'.inv := by
    apply (cancel_mono e'.hom).mp
    rw [Category.assoc, h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [chartOverlap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp, ← h, Functor.map_comp]
  rw [← Category.assoc (overlap p l r k hl hr A).hom,
    overlap_naturality, Category.assoc]
  rw [← Category.assoc ((pullback l).map e.inv), ← Functor.map_comp, hi,
    Functor.map_comp, Category.assoc]

end FLT.Mazur.SchemePullbackOverlap
