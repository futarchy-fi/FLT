/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Normalizing isomorphisms between pullbacks of independent modules

The two source modules may live on different schemes. Normalization on a
test scheme preserves intertwining maps between both independent sources.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentPairNormalization
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y₁ Y₂ Z T : Scheme.{u}} (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
variable (t : T ⟶ Z) (c₁ : T ⟶ Y₁) (c₂ : T ⟶ Y₂)
variable (w₁ : t ≫ l = c₁) (w₂ : t ≫ r = c₂)

/-- Normalize a pair isomorphism while retaining its two independent source modules. -/
def normalize (M₁ : Y₁.Modules) (M₂ : Y₂.Modules)
    (e : (pullback l).obj M₁ ≅ (pullback r).obj M₂) :
    (pullback c₁).obj M₁ ≅ (pullback c₂).obj M₂ :=
  ((comparison t l c₁ w₁).app M₁).symm ≪≫ (pullback t).mapIso e ≪≫
    (comparison t r c₂ w₂).app M₂

/-- Compatible maps on the independent sources remain compatible after normalization. -/
lemma normalize_compatible {M₁ N₁ : Y₁.Modules} {M₂ N₂ : Y₂.Modules}
    (e : (pullback l).obj M₁ ≅ (pullback r).obj M₂)
    (e' : (pullback l).obj N₁ ≅ (pullback r).obj N₂)
    (a : M₁ ⟶ N₁) (b : M₂ ⟶ N₂)
    (h : e.hom ≫ (pullback r).map b = (pullback l).map a ≫ e'.hom) :
    (normalize l r t c₁ c₂ w₁ w₂ M₁ M₂ e).hom ≫ (pullback c₂).map b =
      (pullback c₁).map a ≫ (normalize l r t c₁ c₂ w₁ w₂ N₁ N₂ e').hom := by
  have hl := (comparison t l c₁ w₁).inv.naturality a
  have hr := (comparison t r c₂ w₂).hom.naturality b
  dsimp only [Functor.comp_map] at hl hr
  dsimp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← hr, ← Functor.map_comp_assoc, h, Functor.map_comp]
  simp only [← Category.assoc]
  rw [← hl]

end FLT.Mazur.SchemeIndependentPairNormalization
