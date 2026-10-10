/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquare
public import FLT.Mazur.SchemeModulePullbackUnits

/-!
# Restricting a pullback square along a section

A section of one side of a commutative square reduces its pullback
comparison to the comparison along the retained opposite-side map.
This is the path normalization needed for common-cover reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)
variable (s : X' ⟶ Y') (hs : s ≫ q = 𝟙 X')
variable (t : X' ⟶ Y) (ht : s ≫ b = t) (ha : t ≫ p = a)

/-- Restriction along a section recovers the retained opposite path. -/
@[reassoc]
lemma squareIso_section (A : X.Modules) :
    (pullback s).map ((squareIso p q a b w).hom.app A) ≫
        (comparison s b t ht).hom.app ((pullback p).obj A) ≫
        (comparison t p a ha).hom.app A =
      (retractIso s q hs ((pullback a).obj A)).hom := by
  have hw : s ≫ (b ≫ p) = a := by rw [← Category.assoc, ht, ha]
  have hb := comparison_assoc s b p t (b ≫ p) a ht rfl hw ha A
  have hq := comparison_assoc s q a (𝟙 X') (b ≫ p) a hs w hw (Category.id_comp a) A
  rw [comparison_id_comp] at hq
  have hc : comparison b p (b ≫ p) rfl = pullbackComp b p := by
    simp only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl]
  rw [hc] at hb
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← hb]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  exact hq

/-- Reconstruction on the square restricts to the prescribed covering lift. -/
@[reassoc]
lemma reconstruction_section {A : X.Modules} {M : Y.Modules}
    (e : (pullback p).obj A ≅ M) :
    (pullback s).map
        (((squareIso p q a b w).app A ≪≫ (pullback b).mapIso e).hom) ≫
        (comparison s b t ht).hom.app M =
      (retractIso s q hs ((pullback a).obj A)).hom ≫
        (comparison t p a ha).inv.app A ≫ (pullback t).map e.hom := by
  have hn := (comparison s b t ht).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [hn]
  apply (cancel_epi (retractIso s q hs ((pullback a).obj A)).inv).mp
  have h := squareIso_section p q a b w s hs t ht ha A
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SchemePullbackSquare
