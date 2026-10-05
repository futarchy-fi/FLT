/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Pullback path comparisons across a commutative square

The comparison around a square commutes with normalizing a further pullback
path. The resulting identity compares reconstruction charts on overlap schemes.
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

/-- Compare the two iterated pullbacks around a commutative square. -/
def squareIso : pullback a ⋙ pullback q ≅ pullback p ⋙ pullback b :=
  comparison q a (b ≫ p) w ≪≫ (pullbackComp b p).symm

/-- Normalizing a path after a square agrees with normalizing before the square. -/
@[reassoc]
theorem comparison_square (l : T ⟶ Y') (k : T ⟶ X') (hl : l ≫ q = k)
    (h : (l ≫ b) ≫ p = k ≫ a) (A : X.Modules) :
    (pullback l).map ((squareIso p q a b w).hom.app A) ≫
        (pullbackComp l b).hom.app ((pullback p).obj A) ≫
        (comparison (l ≫ b) p (k ≫ a) h).hom.app A =
      (comparison l q k hl).hom.app ((pullback a).obj A) ≫
        (pullbackComp k a).hom.app A := by
  have hw : l ≫ (b ≫ p) = k ≫ a := by rw [← Category.assoc, h]
  have hb := comparison_assoc l b p (l ≫ b) (b ≫ p) (k ≫ a) rfl rfl hw h A
  have hq := comparison_assoc l q a k (b ≫ p) (k ≫ a) hl w hw rfl A
  have hc (f : Y' ⟶ Y) (g : Y ⟶ X) :
      comparison f g (f ≫ g) rfl = pullbackComp f g := by
    simp [comparison, pullbackCongr]
  have hc' : comparison l b (l ≫ b) rfl = pullbackComp l b := by
    simp [comparison, pullbackCongr]
  have hc'' : comparison k a (k ≫ a) rfl = pullbackComp k a := by
    simp [comparison, pullbackCongr]
  rw [hc b p, hc'] at hb
  rw [hc''] at hq
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [← hb]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact hq

end FLT.Mazur.SchemePullbackSquare
