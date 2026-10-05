/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteDiagramIntegerModel
public import FLT.Mazur.FiniteIntegerModelPullbacks
public import FLT.Mazur.FiniteOpenImmersionIntegerDescent

/-!
# Retaining finite atlas diagrams under approximation

A finite diagram of fixed models can be enlarged until every arrow is an
open immersion and each specified recovered overlap square is cartesian.
The identity, composition, and recovery laws are retained at that same stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

set_option maxHeartbeats 800000 in
-- All arrows and all marked squares share one dependent family of presentations.
/-- Enlarge a finite recovered atlas diagram, retaining equations, opens and pullbacks. -/
theorem exists_integer_model_open_pullback_diagram {A : Type u} [CommRing A]
    {ι : Type v} [SmallCategory ι] [FinCategory ι] (B : ι → Type u)
    [hB : ∀ a, CommRing (B a)] [hAB : ∀ a, Algebra A (B a)]
    (n m : ι → ℕ) (P : ∀ a, Algebra.Presentation A (B a) (Fin (n a)) (Fin (m a)))
    (φ : ∀ {a b}, (a ⟶ b) → (B a →ₐ[A] B b))
    [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ f).toRingHom))]
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [∀ a, (P a).HasCoeffs A₀]
    (φ₀ : ∀ {a b}, (a ⟶ b) →
      ((P a).ModelOfHasCoeffs A₀ →ₐ[A₀] (P b).ModelOfHasCoeffs A₀))
    (hid : ∀ a, φ₀ (𝟙 a) = AlgHom.id A₀ _)
    (hcomp : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), φ₀ (f ≫ g) = (φ₀ g).comp (φ₀ f))
    (hφ : ∀ {a b} (f : a ⟶ b) x, (P b).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ φ₀ f x) =
      φ f ((P a).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x)))
    {K : Type v} [Finite K] (a b c d : K → ι)
    (f : ∀ k, a k ⟶ b k) (g : ∀ k, a k ⟶ c k)
    (i : ∀ k, b k ⟶ d k) (j : ∀ k, c k ⟶ d k)
    (hp : ∀ k, IsPullback (Spec.map (CommRingCat.ofHom (φ (i k)).toRingHom))
      (Spec.map (CommRingCat.ofHom (φ (j k)).toRingHom))
      (Spec.map (CommRingCat.ofHom (φ (f k)).toRingHom))
      (Spec.map (CommRingCat.ofHom (φ (g k)).toRingHom))) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : ∀ a, (P a).HasCoeffs S,
        let ψ := fun {a b} (f : a ⟶ b) ↦ integerModelTransportHom (P a) (P b) h (φ₀ f)
        (∀ a, ψ (𝟙 a) = AlgHom.id S _) ∧
        (∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), ψ (f ≫ g) = (ψ g).comp (ψ f)) ∧
        (∀ {a b} (f : a ⟶ b) x, (P b).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ ψ f x) =
          φ f ((P a).tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ x))) ∧
        (∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (ψ f).toRingHom))) ∧
        ∀ k, IsPullback (Spec.map (CommRingCat.ofHom (ψ (i k)).toRingHom))
          (Spec.map (CommRingCat.ofHom (ψ (j k)).toRingHom))
          (Spec.map (CommRingCat.ofHom (ψ (f k)).toRingHom))
          (Spec.map (CommRingCat.ofHom (ψ (g k)).toRingHom)) := by
  classical
  let : ∀ k, CommRing ((B ∘ a) k) := fun k ↦ hB (a k)
  let : ∀ k, Algebra A ((B ∘ a) k) := fun k ↦ hAB (a k)
  let : ∀ k, (P (a k)).HasCoeffs A₀ := fun k ↦ inferInstance
  let : ∀ k, CommRing ((B ∘ b) k) := fun k ↦ hB (b k)
  let : ∀ k, Algebra A ((B ∘ b) k) := fun k ↦ hAB (b k)
  let : ∀ k, (P (b k)).HasCoeffs A₀ := fun k ↦ inferInstance
  let : ∀ k, CommRing ((B ∘ c) k) := fun k ↦ hB (c k)
  let : ∀ k, Algebra A ((B ∘ c) k) := fun k ↦ hAB (c k)
  let : ∀ k, (P (c k)).HasCoeffs A₀ := fun k ↦ inferInstance
  let : ∀ k, CommRing ((B ∘ d) k) := fun k ↦ hB (d k)
  let : ∀ k, Algebra A ((B ∘ d) k) := fun k ↦ hAB (d k)
  let : ∀ k, (P (d k)).HasCoeffs A₀ := fun k ↦ inferInstance
  obtain ⟨A₁, hA₁, _, h₀₁, ha₁, hb₁, hc₁, hd₁, hp₁⟩ :=
    exists_integer_model_finite_pullbacks (B ∘ a) (B ∘ b) (B ∘ c) (B ∘ d)
      (n ∘ a) (m ∘ a) (n ∘ b) (m ∘ b) (n ∘ c) (m ∘ c) (n ∘ d) (m ∘ d)
      (fun k ↦ P (a k)) (fun k ↦ P (b k)) (fun k ↦ P (c k)) (fun k ↦ P (d k)) A₀
      (fun k ↦ φ₀ (f k)) (fun k ↦ φ₀ (g k)) (fun k ↦ φ₀ (i k)) (fun k ↦ φ₀ (j k))
      (fun k ↦ φ (f k)) (fun k ↦ φ (g k)) (fun k ↦ φ (i k)) (fun k ↦ φ (j k))
      (fun k ↦ hφ (f k)) (fun k ↦ hφ (g k)) (fun k ↦ hφ (i k)) (fun k ↦ hφ (j k))
      hp ∅ Set.finite_empty
  let := hA₁
  let hP₁ : ∀ a, (P a).HasCoeffs A₁ := fun a ↦ integerModel_hasCoeffs_mono (P a) h₀₁
  let ψ₁ := fun {a b} (f : a ⟶ b) ↦ integerModelTransportHom (P a) (P b) h₀₁ (φ₀ f)
  let E := Σ a b : ι, (a ⟶ b)
  let src : E → ι := fun e ↦ e.1
  let dst : E → ι := fun e ↦ e.2.1
  let : ∀ e, CommRing ((B ∘ src) e) := fun e ↦ hB (src e)
  let : ∀ e, Algebra A ((B ∘ src) e) := fun e ↦ hAB (src e)
  let : ∀ e, (P (src e)).HasCoeffs A₁ := fun e ↦ hP₁ (src e)
  let : ∀ e, CommRing ((B ∘ dst) e) := fun e ↦ hB (dst e)
  let : ∀ e, Algebra A ((B ∘ dst) e) := fun e ↦ hAB (dst e)
  let : ∀ e, (P (dst e)).HasCoeffs A₁ := fun e ↦ hP₁ (dst e)
  let : ∀ e : E, IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ e.2.2).toRingHom)) :=
    fun e ↦ inferInstance
  obtain ⟨S, hS, hsS, h₁S, _, _, hopen⟩ :=
    exists_integer_model_finite_openImmersions (B ∘ src) (B ∘ dst)
      (n ∘ src) (m ∘ src) (n ∘ dst) (m ∘ dst)
      (fun e ↦ P (src e)) (fun e ↦ P (dst e)) A₁
      (fun e ↦ ψ₁ e.2.2) (fun e ↦ φ e.2.2)
      (fun e ↦ integerModelTransportHom_recovery (P (src e)) (P (dst e)) h₀₁
        (φ₀ e.2.2) (φ e.2.2) (hφ e.2.2)) s hs
  let hPS : ∀ a, (P a).HasCoeffs S := fun a ↦ integerModel_hasCoeffs_mono (P a) (h₀₁.trans h₁S)
  refine ⟨S, hS, hsS, h₀₁.trans h₁S, hPS, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simp only [hid, integerModelTransportHom_id]
  · intro a b c f g
    simp only [hcomp, integerModelTransportHom_comp]
  · intro a b f x
    exact integerModelTransportHom_recovery (P a) (P b) _ (φ₀ f) (φ f) (hφ f) x
  · intro a b f
    simpa only [ψ₁, integerModelTransportHom_trans] using hopen ⟨a, b, f⟩
  · intro k
    have hpk := integerModelTransportHom_preserves_pullback
      (P (a k)) (P (b k)) (P (c k)) (P (d k)) h₁S
      (ψ₁ (f k)) (ψ₁ (g k)) (ψ₁ (i k)) (ψ₁ (j k)) (hp₁ k)
    simpa only [ψ₁, integerModelTransportHom_trans] using hpk

end FLT.Mazur.Approximation
