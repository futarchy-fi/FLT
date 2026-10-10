/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentNormalizationCoherence

/-!
# Normalization around a square of overlap charts

An actual commuting square gives identical normalized restrictions of an
independent pair isomorphism at the specified common coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentPairNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y₁ Y₂ Z T U V : Scheme.{u}}

/-- The two original paths around a chart square give the same normalized pair map. -/
theorem normalize_square (l : Z ⟶ Y₁) (r : Z ⟶ Y₂)
    (t : T ⟶ Z) (c₁ : T ⟶ Y₁) (c₂ : T ⟶ Y₂)
    (wt₁ : t ≫ l = c₁) (wt₂ : t ≫ r = c₂)
    (u : U ⟶ Z) (b₁ : U ⟶ Y₁) (b₂ : U ⟶ Y₂)
    (wu₁ : u ≫ l = b₁) (wu₂ : u ≫ r = b₂)
    (s : V ⟶ T) (v : V ⟶ U) (a₁ : V ⟶ Y₁) (a₂ : V ⟶ Y₂)
    (ws₁ : s ≫ c₁ = a₁) (ws₂ : s ≫ c₂ = a₂)
    (wv₁ : v ≫ b₁ = a₁) (wv₂ : v ≫ b₂ = a₂) (w : s ≫ t = v ≫ u)
    (M₁ : Y₁.Modules) (M₂ : Y₂.Modules)
    (e : (pullback l).obj M₁ ≅ (pullback r).obj M₂) :
    normalize c₁ c₂ s a₁ a₂ ws₁ ws₂ M₁ M₂
        (normalize l r t c₁ c₂ wt₁ wt₂ M₁ M₂ e) =
      normalize b₁ b₂ v a₁ a₂ wv₁ wv₂ M₁ M₂
        (normalize l r u b₁ b₂ wu₁ wu₂ M₁ M₂ e) := by
  have h₁ : (v ≫ u) ≫ l = a₁ := by rw [Category.assoc, wu₁, wv₁]
  have h₂ : (v ≫ u) ≫ r = a₂ := by rw [Category.assoc, wu₂, wv₂]
  rw [normalize_normalize l r t c₁ c₂ wt₁ wt₂ s (v ≫ u) w
    a₁ a₂ ws₁ ws₂ h₁ h₂]
  rw [normalize_normalize l r u b₁ b₂ wu₁ wu₂ v (v ≫ u) rfl
    a₁ a₂ wv₁ wv₂ h₁ h₂]

end FLT.Mazur.SchemeIndependentPairNormalization
