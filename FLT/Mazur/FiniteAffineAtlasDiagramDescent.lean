/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelAtlasDiagram

/-!
# Constructing finite affine atlas diagram models

A finite diagram of finitely presented affine algebras, with open restriction
maps and specified cartesian overlap squares, has a model over a finite-type
integer coefficient ring. The model is constructed, including its arrows,
identity and composition laws, open immersions, and overlap pullbacks.
This is diagram descent; constructing a cover and gluing a scheme are separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Construct a common model of a finite affine atlas diagram and its overlap squares. -/
theorem exists_finite_affine_atlas_diagram_model {A : Type u} [CommRing A]
    {ι : Type v} [SmallCategory ι] [FinCategory ι] (B : ι → Type u)
    [∀ a, CommRing (B a)] [∀ a, Algebra A (B a)]
    (n m : ι → ℕ) (P : ∀ a, Algebra.Presentation A (B a) (Fin (n a)) (Fin (m a)))
    (φ : ∀ {a b}, (a ⟶ b) → (B a →ₐ[A] B b))
    [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ f).toRingHom))]
    (hid : ∀ a, φ (𝟙 a) = AlgHom.id A _)
    (hcomp : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), φ (f ≫ g) = (φ g).comp (φ f))
    {K : Type v} [Finite K] (a b c d : K → ι)
    (f : ∀ k, a k ⟶ b k) (g : ∀ k, a k ⟶ c k)
    (i : ∀ k, b k ⟶ d k) (j : ∀ k, c k ⟶ d k)
    (hp : ∀ k, IsPullback (Spec.map (CommRingCat.ofHom (φ (i k)).toRingHom))
      (Spec.map (CommRingCat.ofHom (φ (j k)).toRingHom))
      (Spec.map (CommRingCat.ofHom (φ (f k)).toRingHom))
      (Spec.map (CommRingCat.ofHom (φ (g k)).toRingHom))) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ _hP : ∀ a, (P a).HasCoeffs S,
        ∃ ψ : ∀ {a b}, (a ⟶ b) →
          ((P a).ModelOfHasCoeffs S →ₐ[S] (P b).ModelOfHasCoeffs S),
        (∀ a, ψ (𝟙 a) = AlgHom.id S _) ∧
        (∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), ψ (f ≫ g) = (ψ g).comp (ψ f)) ∧
        (∀ {a b} (f : a ⟶ b) x, (P b).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ ψ f x) =
          φ f ((P a).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ x))) ∧
        (∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (ψ f).toRingHom))) ∧
        ∀ k, IsPullback (Spec.map (CommRingCat.ofHom (ψ (i k)).toRingHom))
          (Spec.map (CommRingCat.ofHom (ψ (j k)).toRingHom))
          (Spec.map (CommRingCat.ofHom (ψ (f k)).toRingHom))
          (Spec.map (CommRingCat.ofHom (ψ (g k)).toRingHom)) := by
  obtain ⟨A₀, hA₀, _, hP₀, φ₀, hid₀, hcomp₀, hφ₀, _⟩ :=
    exists_integer_model_diagram B n m P φ hid hcomp (fun _ ↦ PEmpty)
      (fun _ k ↦ k.elim) (fun _ k ↦ k.elim) ∅ Set.finite_empty
  let := hA₀
  let := hP₀
  obtain ⟨S, hS, hsS, h, hPS, hlaws⟩ :=
    exists_integer_model_open_pullback_diagram B n m P φ A₀ φ₀ hid₀ hcomp₀ hφ₀
      a b c d f g i j hp s hs
  let := hPS
  exact ⟨S, hS, hsS, hPS,
    fun {a b} f ↦ integerModelTransportHom (P a) (P b) h (φ₀ f), hlaws⟩

end FLT.Mazur.Approximation
