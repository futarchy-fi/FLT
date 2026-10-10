/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquare

/-!
# Pullback square comparisons with named test paths

Normalize both branches of a pulled-back square to independently named
scheme maps. Associativity proves the comparison equation without
unfolding the module pullback construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' T : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

/-- Normalizing either branch of a square gives the same named test pullback. -/
@[reassoc]
lemma comparison_square_named (s : T ⟶ Y') (k : T ⟶ X') (t : T ⟶ Y)
    (z : T ⟶ X) (hk : s ≫ q = k) (ht : s ≫ b = t)
    (ha : k ≫ a = z) (hp : t ≫ p = z) (A : X.Modules) :
    (pullback s).map ((squareIso p q a b w).hom.app A) ≫
        (comparison s b t ht).hom.app ((pullback p).obj A) ≫
        (comparison t p z hp).hom.app A =
      (comparison s q k hk).hom.app ((pullback a).obj A) ≫
        (comparison k a z ha).hom.app A := by
  have hw : s ≫ (b ≫ p) = z := by rw [← Category.assoc, ht, hp]
  have hb := comparison_assoc s b p t (b ≫ p) z ht rfl hw hp A
  have hq := comparison_assoc s q a k (b ≫ p) z hk w hw ha A
  have hc : comparison b p (b ≫ p) rfl = pullbackComp b p := by
    simp only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl]
  rw [hc] at hb
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← hb]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  exact hq

end FLT.Mazur.SchemePullbackSquare
