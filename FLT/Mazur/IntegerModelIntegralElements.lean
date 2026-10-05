/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelMonicLifts
public import FLT.Mazur.IntegerModelEventualEquality
public import FLT.Mazur.PrincipalChartIntegerDescent
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Descending integrality of finitely many model elements

Lift monic witnesses over the source model, then kill their evaluations
in the target model. This does not require recovery to be injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Integrality of a finite family descends along the transported model map. -/
theorem exists_integer_model_integral_elements {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] C)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    {I : Type v} [Finite I] (x : I → Q.ModelOfHasCoeffs A₀)
    (hx : ∀ i, φ.toRingHom.IsIntegralElem
      (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x i)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        ∀ i, (integerModelTransportHom P Q h f).toRingHom.IsIntegralElem
          (integerModelTransition Q h (x i)) := by
  classical
  choose p hp heval using hx
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, q, hq, hrec⟩ :=
    exists_integer_model_monic_lifts P A₀ p hp s hs
  let := hA₁
  let := hP₁
  let hQ₁ : Q.HasCoeffs A₁ := integerModel_hasCoeffs_mono Q h₀₁
  let f₁ := integerModelTransportHom P Q h₀₁ f
  let x₁ := fun i ↦ integerModelTransition Q h₀₁ (x i)
  let z := fun i ↦ (q i).eval₂ f₁.toRingHom (x₁ i)
  have hcomm : (integerModelRecoveryHom Q).toRingHom.comp f₁.toRingHom =
      φ.toRingHom.comp (integerModelRecoveryHom P).toRingHom := by
    apply RingHom.ext
    intro b
    exact integerModelTransportHom_recovery P Q h₀₁ f φ hf b
  have hz (i) : Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ z i) = 0 := by
    change (integerModelRecoveryHom Q).toRingHom ((q i).eval₂ f₁.toRingHom (x₁ i)) = 0
    rw [hom_eval₂, hcomm, ← eval₂_map, hrec]
    change (p i).eval₂ φ.toRingHom
      (Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ x₁ i)) = 0
    rw [integerModelTransition_recovery]
    exact heval i
  obtain ⟨S, hS, hsS, h₁S, hQS, hzS⟩ :=
    exists_integer_model_eventual_zero Q A₁ z hz s hs
  let := hQS
  let hPS : P.HasCoeffs S := integerModel_hasCoeffs_mono P h₁S
  let fS := integerModelTransportHom P Q h₁S f₁
  have hcommS : fS.toRingHom.comp (integerModelTransition P h₁S) =
      (integerModelTransition Q h₁S).comp f₁.toRingHom := by
    apply RingHom.ext
    intro b
    exact integerModelTransportHom_transition P Q h₁S f₁ b
  refine ⟨S, hS, hsS, h₀₁.trans h₁S, hPS, hQS, fun i ↦ ?_⟩
  rw [← integerModelTransportHom_trans P Q h₀₁ h₁S,
    ← integerModelTransition_trans Q h₀₁ h₁S]
  refine ⟨(q i).map (integerModelTransition P h₁S), (hq i).map _, ?_⟩
  change ((q i).map _).eval₂ fS.toRingHom (integerModelTransition Q h₁S (x₁ i)) = 0
  rw [eval₂_map, hcommS, ← hom_eval₂]
  exact hzS i

end FLT.Mazur.Approximation
