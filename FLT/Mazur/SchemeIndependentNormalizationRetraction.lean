/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentNormalizationCoherence

/-!
# Retractions of independent overlap charts

Normalizing to an identity chart does nothing. A chart and a left inverse
therefore recover the exact original isomorphism, with its original endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentPairNormalization
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y₁ Y₂ Z T : Scheme.{u}}

/-- Identity normalization retains the exact original map. -/
theorem normalize_identity (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
    (M₁ : Y₁.Modules) (M₂ : Y₂.Modules)
    (e : (pullback l).obj M₁ ≅ (pullback r).obj M₂) :
    normalize l r (𝟙 Z) l r (Category.id_comp l) (Category.id_comp r) M₁ M₂ e = e := by
  apply Iso.ext
  apply (cancel_epi ((comparison (𝟙 Z) l l (Category.id_comp l)).hom.app M₁)).mp
  simp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Iso.hom_inv_id_app_assoc]
  rw [comparison_id_comp, comparison_id_comp]
  exact (pullbackId Z).hom.naturality e.hom

/-- A return chart recovers the original pair map through its prescribed coordinates. -/
theorem normalize_retract (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
    (t : T ⟶ Z) (s : Z ⟶ T) (hs : s ≫ t = 𝟙 Z)
    (c₁ : T ⟶ Y₁) (c₂ : T ⟶ Y₂) (w₁ : t ≫ l = c₁) (w₂ : t ≫ r = c₂)
    (v₁ : s ≫ c₁ = l) (v₂ : s ≫ c₂ = r)
    (M₁ : Y₁.Modules) (M₂ : Y₂.Modules)
    (e : (pullback l).obj M₁ ≅ (pullback r).obj M₂) :
    normalize c₁ c₂ s l r v₁ v₂ M₁ M₂
      (normalize l r t c₁ c₂ w₁ w₂ M₁ M₂ e) = e := by
  rw [normalize_normalize l r t c₁ c₂ w₁ w₂ s (𝟙 Z) hs l r v₁ v₂
    (Category.id_comp l) (Category.id_comp r), normalize_identity]

end FLT.Mazur.SchemeIndependentPairNormalization
