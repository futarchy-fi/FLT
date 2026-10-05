/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquare

/-!
# Unit coherence for pullback squares

The square comparison for identity refinements agrees with the actual
pullback unit comparisons, including their effect on reconstruction charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}

/-- Either route around a square has the same normalized pullback. -/
@[reassoc]
theorem squareIso_comparison (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : q ≫ a = b ≫ p) (k : Y' ⟶ X) (hq : q ≫ a = k) (hb : b ≫ p = k)
    (A : X.Modules) :
    (squareIso p q a b w).hom.app A ≫ (comparison b p k hb).hom.app A =
      (comparison q a k hq).hom.app A := by
  cases hb
  have hc : comparison b p (b ≫ p) rfl = pullbackComp b p := by
    simp only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl]
  rw [hc]
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The identity square respects both pullback unit comparisons. -/
@[reassoc]
theorem squareIso_identity (p : Y ⟶ X) (A : X.Modules) :
    (squareIso p p (𝟙 X) (𝟙 Y) (by simp)).hom.app A ≫
        (pullbackId Y).hom.app ((pullback p).obj A) =
      (pullback p).map ((pullbackId X).hom.app A) := by
  have h := squareIso_comparison p p (𝟙 X) (𝟙 Y) (by simp) p
    (Category.comp_id p) (Category.id_comp p) A
  rw [comparison_id_comp, comparison_comp_id] at h
  exact h

/-- The pullback unit comparison for a map known to be the identity. -/
def identityIso (a : X ⟶ X) (ha : a = 𝟙 X) : pullback a ≅ 𝟭 X.Modules :=
  pullbackCongr ha ≪≫ pullbackId X

/-- Identity refinement of a reconstruction respects the actual unit charts. -/
@[reassoc]
theorem reconstruction_identity (p : Y ⟶ X) (a : X ⟶ X) (b : Y ⟶ Y)
    (ha : a = 𝟙 X) (hb : b = 𝟙 Y) (w : p ≫ a = b ≫ p)
    {A : X.Modules} {M : Y.Modules} (e : (pullback p).obj A ≅ M) :
    (squareIso p p a b w).hom.app A ≫ (pullback b).map e.hom ≫
        (identityIso b hb).hom.app M =
      (pullback p).map ((identityIso a ha).hom.app A) ≫ e.hom := by
  subst a b
  change (squareIso p p (𝟙 X) (𝟙 Y) w).hom.app A ≫
      (pullback (𝟙 Y)).map e.hom ≫ (pullbackId Y).hom.app M =
    (pullback p).map ((pullbackId X).hom.app A) ≫ e.hom
  rw [(pullbackId Y).hom.naturality e.hom]
  change _ = (pullback p).map ((pullbackId X).hom.app A) ≫ e.hom
  rw [← Category.assoc, squareIso_identity]
  rfl

end FLT.Mazur.SchemePullbackSquare
