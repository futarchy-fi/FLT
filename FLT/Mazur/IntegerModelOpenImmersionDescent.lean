/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelCoverDescent
public import FLT.Mazur.IntegerModelOpenImmersionRefinement

/-!
# Descent of affine open immersions between fixed integer models

A fixed model map recovering an affine open immersion becomes an open immersion
at a later finite-type integer stage. Denominators and cover witnesses are
constructed from the original map, without assuming flatness of recovery.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A map of fixed presentation models recovering an open immersion eventually
becomes an open immersion, with no extra hypothesis on its principal charts. -/
theorem exists_integer_model_openImmersion {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] C) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        IsOpenImmersion (Spec.map
          (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) := by
  classical
  obtain ⟨t, hcover, ht⟩ := exists_finite_principal_target_refinement φ.toRingHom
  change (⨆ i : t, PrimeSpectrum.basicOpen (φ (i : B))) = ⊤ at hcover
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, x, hx⟩ :=
    exists_fixed_model_element_lifts P A₀ (fun i : t ↦ (i : B)) ∅ Set.finite_empty
  let := hA₁
  let := hP₁
  let hQ₁ : Q.HasCoeffs A₁ := integerModel_hasCoeffs_mono Q h₀₁
  let f₁ := integerModelTransportHom P Q h₀₁ f
  have hf₁ := integerModelTransportHom_recovery P Q h₀₁ f φ hf
  have hc₁ : (⨆ i : t, PrimeSpectrum.basicOpen
      (Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ f₁ (x i)))) = ⊤ := by
    simpa only [f₁, hf₁, hx] using hcover
  obtain ⟨A₂, hA₂, _, h₁₂, hQ₂, _, _, hc₂⟩ :=
    exists_integer_model_principal_cover Q A₁ (fun i ↦ f₁ (x i)) hc₁ ∅ Set.finite_empty
  let := hA₂
  let := hQ₂
  let hP₂ : P.HasCoeffs A₂ := integerModel_hasCoeffs_mono P h₁₂
  let f₂ := integerModelTransportHom P Q h₁₂ f₁
  let x₂ := fun i ↦ integerModelTransition P h₁₂ (x i)
  have hf₂ := integerModelTransportHom_recovery P Q h₁₂ f₁ φ hf₁
  have hcover₂ : (⨆ i, PrimeSpectrum.basicOpen (f₂ (x₂ i))) = ⊤ := by
    simpa only [f₂, x₂, integerModelTransportHom_transition] using hc₂
  have hx₂ (i : t) : (PrimeSpectrum.basicOpen
      (P.tensorModelOfHasCoeffsEquiv A₂ (1 ⊗ₜ x₂ i)) : Set (PrimeSpectrum B)) ⊆
        Set.range (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    simpa only [x₂, integerModelTransition_recovery, hx] using ht i i.property
  obtain ⟨S, hS, hsS, h₂S, hPS, hQS, hopen⟩ :=
    exists_integer_model_openImmersion_of_refinement P Q A₂ f₂ φ hf₂ x₂ hcover₂ hx₂ s hs
  let := hPS
  let := hQS
  refine ⟨S, hS, hsS, h₀₁.trans (h₁₂.trans h₂S), hPS, hQS, ?_⟩
  simpa only [f₂, f₁, integerModelTransportHom_trans] using hopen

end FLT.Mazur.Approximation
