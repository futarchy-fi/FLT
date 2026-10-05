/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalComparisonRecovery

/-!
# Open immersions from descended principal comparisons

An equivalence compatible with a principal chart makes the chart map an
open immersion. Applying this to eventual model comparisons gives an open
immersion for the transported map at a finite coefficient stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- An identified principal localization gives an open immersion for its actual map. -/
theorem principalComparison_isOpenImmersion {R S : Type u} [CommRing R] [CommRing S]
    (x : R) (f : R →+* S) (e : Localization.Away x ≃+* S)
    (he : ∀ r, e (algebraMap R (Localization.Away x) r) = f r) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  let := f.toAlgebra
  let e' : Localization.Away x ≃ₐ[R] S := { e with commutes' := he }
  let : IsLocalization.Away x S :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers x) e'
  exact IsOpenImmersion.of_isLocalization x

/-- A principal chart with a recovered factorization becomes an open immersion
of fixed presentation models after enlargement. -/
theorem exists_integer_model_principal_openImmersion {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    (x : P.ModelOfHasCoeffs A₀)
    (Q : Algebra.Presentation A
      (Localization.Away (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x))) (Fin r) (Fin t))
    [Q.HasCoeffs A₀]
    (F : Localization.Away x →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (hF : ∀ b, F (algebraMap _ (Localization.Away x) b) = f b)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁, ∃ _hQ : Q.HasCoeffs A₁,
        IsOpenImmersion (Spec.map
          (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) := by
  obtain ⟨A₁, hA₁, hs₁, h, hP₁, hQ₁, e₁, he₁⟩ :=
    exists_integer_model_principal_chart_isomorphism P A₀ x Q F f hF hf s hs
  let := hP₁
  let := hQ₁
  exact ⟨A₁, hA₁, hs₁, h, hP₁, hQ₁,
    principalComparison_isOpenImmersion (integerModelTransition P h x)
      (integerModelTransportHom P Q h f).toRingHom e₁.toRingEquiv he₁⟩

/-- The open-immersion criterion permits an explicitly identified recovered element. -/
theorem exists_integer_model_principal_openImmersion_of_eq {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    (x : P.ModelOfHasCoeffs A₀) (z : B)
    (hx : P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x) = z)
    (Q : Algebra.Presentation A (Localization.Away z) (Fin r) (Fin t))
    [Q.HasCoeffs A₀]
    (F : Localization.Away x →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (hF : ∀ b, F (algebraMap _ (Localization.Away x) b) = f b)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁, ∃ _hQ : Q.HasCoeffs A₁,
        IsOpenImmersion (Spec.map
          (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) := by
  subst z
  exact exists_integer_model_principal_openImmersion P A₀ x Q F f hF hf s hs

end FLT.Mazur.Approximation
