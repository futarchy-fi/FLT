/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalIntegerModelIsomorphism

/-!
# Recovery and chart compatibility of principal comparisons

Recovery on the original chart determines recovery on its localization.
An eventual principal isomorphism then retains the entire transported chart
map, not only the image of the old source model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
  (A₀ : Subalgebra ℤ A) [P.HasCoeffs A₀] (x : P.ModelOfHasCoeffs A₀)
  (Q : Algebra.Presentation A
    (Localization.Away (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x))) (Fin r) (Fin t))
  [Q.HasCoeffs A₀]
  (F : Localization.Away x →ₐ[A₀] Q.ModelOfHasCoeffs A₀)

/-- Agreement on the chart determines recovery on every localized element. -/
theorem integerPrincipalComparison_recovery
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀
      (1 ⊗ₜ F (algebraMap _ (Localization.Away x) b)) =
        algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (c : Localization.Away x) :
    Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ F c) =
      principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x (1 ⊗ₜ c) := by
  let g := (integerModelRecoveryHom Q (A₀ := A₀)).toRingHom.comp F.toRingHom
  let k := (principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom
  have heq : g = k := by
    apply IsLocalization.ringHom_ext (Submonoid.powers x)
    apply RingHom.ext
    intro b
    change Q.tensorModelOfHasCoeffsEquiv A₀
      (1 ⊗ₜ F (algebraMap _ (Localization.Away x) b)) =
        principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x
          (1 ⊗ₜ algebraMap _ (Localization.Away x) b)
    rw [principalIntegerModelEquiv_tmul, hf]
  exact RingHom.congr_fun heq c

set_option maxHeartbeats 800000 in
-- The comparison simultaneously elaborates three finite coefficient stages.
/-- A recovered principal comparison becomes an equivalence retaining the
whole chart map after coefficient enlargement. -/
theorem exists_integer_model_principal_chart_isomorphism [Algebra.FiniteType ℤ A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (hF : ∀ b, F (algebraMap _ (Localization.Away x) b) = f b)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁, ∃ _hQ : Q.HasCoeffs A₁,
        ∃ e₁ : Localization.Away (integerModelTransition P h x) ≃ₐ[A₁]
            Q.ModelOfHasCoeffs A₁,
          ∀ b, e₁ (algebraMap _ (Localization.Away (integerModelTransition P h x)) b) =
            integerModelTransportHom P Q h f b := by
  have hrec := integerPrincipalComparison_recovery P A₀ x Q F (by
    intro b
    rw [hF, hf])
  obtain ⟨A₁, hA₁, hs₁, h, hP₁, hQ₁, e₁, he₁⟩ :=
    exists_integer_model_principal_isomorphism P A₀ x Q F hrec s hs
  let := hP₁
  let := hQ₁
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have heq : e₁.toAlgHom.comp
      (IsScalarTower.toAlgHom A₁ (P.ModelOfHasCoeffs A₁)
        (Localization.Away (integerModelTransition P h x))) =
      integerModelTransportHom P Q h f := by
    apply integerModel_hom_ext P h
    intro b
    change e₁ (algebraMap _ (Localization.Away (integerModelTransition P h x))
      (integerModelTransition P h b)) =
        integerModelTransportHom P Q h f (integerModelTransition P h b)
    rw [integerModelTransportHom_transition]
    simpa [hF] using he₁ (algebraMap _ (Localization.Away x) b)
  exact ⟨A₁, hA₁, hs₁, h, hP₁, hQ₁, e₁, fun b ↦ AlgHom.congr_fun heq b⟩

end FLT.Mazur.Approximation
