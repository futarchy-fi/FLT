/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackCoordinateRecovery

/-!
# Normalized pair equations retain independent coordinate recoveries

A pair equation expressed through independent source recoveries survives
further normalization, using the same recoveries for shared coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentRecoveryNormalization
open SheafPullbackPathComparison SheafPullbackCoordinateRecovery
open SchemeIndependentPairNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Y₁ Y₂ Z T : Scheme.{u}}

/-- Normalized pair equations commute with the original source recoveries. -/
lemma normalize_recovery (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
    (i₁ : Y₁ ⟶ Y) (i₂ : Y₂ ⟶ Y) (c₁ c₂ : Z ⟶ Y)
    (w₁ : l ≫ i₁ = c₁) (w₂ : r ≫ i₂ = c₂)
    (t : T ⟶ Z) (d₁ : T ⟶ Y₁) (d₂ : T ⟶ Y₂) (z₁ z₂ : T ⟶ Y)
    (v₁ : t ≫ l = d₁) (v₂ : t ≫ r = d₂)
    (u₁ : t ≫ c₁ = z₁) (u₂ : t ≫ c₂ = z₂)
    (w₁' : d₁ ≫ i₁ = z₁) (w₂' : d₂ ≫ i₂ = z₂)
    (M : Y.Modules) {N₁ : Y₁.Modules} {N₂ : Y₂.Modules}
    (a₁ : (pullback i₁).obj M ≅ N₁) (a₂ : (pullback i₂).obj M ≅ N₂)
    (e : (pullback c₁).obj M ≅ (pullback c₂).obj M)
    (e' : (pullback l).obj N₁ ≅ (pullback r).obj N₂)
    (he : e.hom ≫ (recovery r i₂ c₂ w₂ M a₂).hom =
      (recovery l i₁ c₁ w₁ M a₁).hom ≫ e'.hom) :
    (normalize c₁ c₂ t z₁ z₂ u₁ u₂ M M e).hom ≫
        (recovery d₂ i₂ z₂ w₂' M a₂).hom =
      (recovery d₁ i₁ z₁ w₁' M a₁).hom ≫
        (normalize l r t d₁ d₂ v₁ v₂ N₁ N₂ e').hom := by
  apply (cancel_epi ((comparison t c₁ z₁ u₁).hom.app M)).mp
  dsimp only [SchemeIndependentPairNormalization.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← recovery_pullback r i₂ c₂ w₂ t d₂ z₂ v₂ u₂ w₂' M a₂]
  rw [← Functor.map_comp_assoc, he, Functor.map_comp]
  rw [← Category.assoc ((comparison t c₁ z₁ u₁).hom.app M),
    ← recovery_pullback l i₁ c₁ w₁ t d₁ z₁ v₁ u₁ w₁' M a₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SchemeIndependentRecoveryNormalization
