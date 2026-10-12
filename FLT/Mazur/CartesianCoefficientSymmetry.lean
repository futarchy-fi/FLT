/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Coefficient symmetries on an actual Cartesian square

A base symmetry lifts uniquely while fixing the original object projection.
Composition, involution, and naturality follow from the two retained
projections; no trivialization or descent comparison is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.CartesianCoefficientSymmetry
universe u v
variable {C : Type u} [Category.{v} C]
  {B S X Y : C} {p : Y ⟶ X} {s : Y ⟶ S} {f : X ⟶ B} {q : S ⟶ B}
  (H : IsPullback p s f q) (σ : S ⟶ S) (hσ : σ ≫ q = q)

/-- The actual lift changes only the coefficient projection. -/
def map : Y ⟶ Y := H.lift p (s ≫ σ) (by rw [Category.assoc, hσ]; exact H.w)

/-- The original object projection is unchanged. -/
@[reassoc (attr := simp)] theorem map_original : map H σ hσ ≫ p = p :=
  H.lift_fst _ _ _

/-- The coefficient projection changes by the specified symmetry. -/
@[reassoc (attr := simp)] theorem map_coefficient : map H σ hσ ≫ s = s ≫ σ :=
  H.lift_snd _ _ _

/-- The identity coefficient map induces the identity on the original pullback. -/
@[simp] theorem map_id : map H (𝟙 S) (Category.id_comp q) = 𝟙 Y := by
  apply H.hom_ext <;> simp

/-- Composition of coefficient symmetries is the actual composite of their lifts. -/
theorem map_comp (τ : S ⟶ S) (hτ : τ ≫ q = q) :
    map H σ hσ ≫ map H τ hτ =
      map H (σ ≫ τ) (by rw [Category.assoc, hτ, hσ]) := by
  apply H.hom_ext <;> simp

/-- An involutive coefficient operation squares to the identity on the whole pullback. -/
@[reassoc] theorem map_involutive (hσσ : σ ≫ σ = 𝟙 S) :
    map H σ hσ ≫ map H σ hσ = 𝟙 Y := by
  apply H.hom_ext <;> simp [Category.assoc, hσσ]

/-- The lifted involution is a concrete automorphism, with both projections retained. -/
def involutionIso (hσσ : σ ≫ σ = 𝟙 S) : Y ≅ Y where
  hom := map H σ hσ
  inv := map H σ hσ
  hom_inv_id := map_involutive H σ hσ hσσ
  inv_hom_id := map_involutive H σ hσ hσσ

/-- A morphism between actual coefficient squares commutes with their lifted symmetries. -/
@[reassoc] theorem map_naturality {X' Y' : C} {p' : Y' ⟶ X'} {s' : Y' ⟶ S}
    {f' : X' ⟶ B} (H' : IsPullback p' s' f' q)
    (a : Y ⟶ Y') (b : X ⟶ X') (hp : a ≫ p' = p ≫ b) (hs : a ≫ s' = s) :
    map H σ hσ ≫ a = a ≫ map H' σ hσ := by
  apply H'.hom_ext
  · simp only [Category.assoc, hp, map_original_assoc, map_original]
  · simp only [Category.assoc, map_coefficient, hs, reassoc_of% hs]

end FLT.Mazur.CartesianCoefficientSymmetry
