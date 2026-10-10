/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentPairNormalization
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Coherence of independent pair normalization

Iterated normalization is normalization along the named composite map.
Composition is preserved with the original coordinate charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentPairNormalization
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y₁ Y₂ Y₃ Z T U : Scheme.{u}}

/-- Further normalization agrees with the original normalization at the composite chart. -/
theorem normalize_normalize (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
    (t : T ⟶ Z) (c₁ : T ⟶ Y₁) (c₂ : T ⟶ Y₂)
    (w₁ : t ≫ l = c₁) (w₂ : t ≫ r = c₂)
    (s : U ⟶ T) (d : U ⟶ Z) (wd : s ≫ t = d)
    (b₁ : U ⟶ Y₁) (b₂ : U ⟶ Y₂)
    (v₁ : s ≫ c₁ = b₁) (v₂ : s ≫ c₂ = b₂)
    (u₁ : d ≫ l = b₁) (u₂ : d ≫ r = b₂)
    (M₁ : Y₁.Modules) (M₂ : Y₂.Modules)
    (e : (pullback l).obj M₁ ≅ (pullback r).obj M₂) :
    normalize c₁ c₂ s b₁ b₂ v₁ v₂ M₁ M₂ (normalize l r t c₁ c₂ w₁ w₂ M₁ M₂ e) =
      normalize l r d b₁ b₂ u₁ u₂ M₁ M₂ e := by
  apply Iso.ext
  apply (cancel_epi ((comparison s c₁ b₁ v₁).hom.app M₁)).mp
  change (comparison s c₁ b₁ v₁).hom.app M₁ ≫
      SheafPullbackMapNormalization.normalize s c₁ c₂ b₁ b₂ v₁ v₂
        (SheafPullbackMapNormalization.normalize t l r c₁ c₂ w₁ w₂ e.hom) = _
  rw [SheafPullbackMapNormalization.normalize_comm]
  exact SheafPullbackMapNormalization.normalize_refine t l r c₁ c₂ w₁ w₂
    s d wd b₁ b₂ v₁ v₂ u₁ u₂ e.hom

/-- Normalization preserves composition with its exact shared middle coordinate. -/
theorem normalize_trans (l : Z ⟶ Y₁) (m : Z ⟶ Y₂) (r : Z ⟶ Y₃)
    (t : T ⟶ Z) (c₁ : T ⟶ Y₁) (c₂ : T ⟶ Y₂) (c₃ : T ⟶ Y₃)
    (w₁ : t ≫ l = c₁) (w₂ : t ≫ m = c₂) (w₃ : t ≫ r = c₃)
    (M₁ : Y₁.Modules) (M₂ : Y₂.Modules) (M₃ : Y₃.Modules)
    (a : (pullback l).obj M₁ ≅ (pullback m).obj M₂)
    (b : (pullback m).obj M₂ ≅ (pullback r).obj M₃) :
    normalize l r t c₁ c₃ w₁ w₃ M₁ M₃ (a ≪≫ b) =
      normalize l m t c₁ c₂ w₁ w₂ M₁ M₂ a ≪≫
        normalize m r t c₂ c₃ w₂ w₃ M₂ M₃ b := by
  apply Iso.ext
  simp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SchemeIndependentPairNormalization
