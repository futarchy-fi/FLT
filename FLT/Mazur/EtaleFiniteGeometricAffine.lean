/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteGeometricDiagram

/-!
# Affine common étale neighborhoods retaining the whole geometric test

A field test factors through an affine open around its single image point.
Apply this to the actual finite pullback diagram: all original morphism
identities survive on a common affine étale neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleFiniteGeometricDiagram
universe u
variable {Y : Scheme.{u}} {K : Type u} [Field K]

/-- A geometric test factors through an affine open inside any prescribed neighborhood. -/
theorem exists_affine_factor (b : Spec (.of K) ⟶ Y) (W : Y.Opens)
    (hb : b default ∈ W) :
    ∃ (U : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U),
      IsAffine U ∧ IsOpenImmersion q ∧ z ≫ q = b ∧ Set.range q ⊆ W := by
  obtain ⟨O, hO, hbO, hOW⟩ := exists_isAffineOpen_mem_and_subset hb
  have hr : Set.range b ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change b x ∈ O
    rwa [Subsingleton.elim x (default : Spec (.of K))]
  exact ⟨O.toScheme, O.ι, IsOpenImmersion.lift O.ι b hr, hO, inferInstance,
    IsOpenImmersion.lift_fac O.ι b hr, by rwa [Scheme.Opens.range_ι]⟩

/-- Finite geometric lifts spread exactly on one affine étale neighborhood of the original base. -/
theorem exists_common_affine {n : ℕ} (X : Fin n → Scheme.{u}) (f : ∀ i, X i ⟶ Y)
    [∀ i, Etale (f i)] (b : Spec (.of K) ⟶ Y) (a : ∀ i, Spec (.of K) ⟶ X i)
    (ha : ∀ i, a i ≫ f i = b) :
    ∃ (U : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U) (r : ∀ i, U ⟶ X i),
      IsAffine U ∧ Etale q ∧ z ≫ q = b ∧ (∀ i, r i ≫ f i = q) ∧
      (∀ i, z ≫ r i = a i) := by
  obtain ⟨U, q, z, r, hq, hz, hr, he⟩ := exists_common X f b a ha
  obtain ⟨W, j, w, hW, hj, hw, _⟩ := exists_affine_factor z ⊤ (by trivial)
  refine ⟨W, j ≫ q, w, fun i ↦ j ≫ r i, hW, inferInstance, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hw, hz]
  · intro i
    rw [Category.assoc, hr]
  · intro i
    rw [← Category.assoc, hw, he]

end FLT.Mazur.EtaleFiniteGeometricDiagram
