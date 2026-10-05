/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelEventualUnits
public import FLT.Mazur.PrincipalOpenIntegerModel

/-!
# Factoring a descended map through a principal chart

If the image of a marked source element recovers a unit, enlargement makes
the transported map factor through the localization of the source model.
The resulting comparison commutes with the source map at the finite stage.
Its invertibility is a separate condition, not part of this construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A fixed model map factors through a marked principal localization after
enlarging coefficients if the marked image recovers a unit. -/
theorem exists_integer_model_principal_comparison {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (x : P.ModelOfHasCoeffs A₀) (y : Cˣ)
    (hy : Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f x) = (y : C))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁, ∃ _hQ : Q.HasCoeffs A₁,
        ∃ F : Localization.Away (integerModelTransition P h x) →ₐ[A₁]
            Q.ModelOfHasCoeffs A₁,
          ∀ b, F (algebraMap (P.ModelOfHasCoeffs A₁)
            (Localization.Away (integerModelTransition P h x)) b) =
              integerModelTransportHom P Q h f b := by
  obtain ⟨A₁, hA₁, hs₁, h, hQ₁, y₁, hy₁⟩ :=
    exists_integer_model_eventual_units Q A₀ (fun _ : Unit ↦ f x) (fun _ ↦ y)
      (fun _ ↦ hy) s hs
  let := hQ₁
  let : P.HasCoeffs A₁ := integerModel_hasCoeffs_mono P h
  let f₁ := integerModelTransportHom P Q h f
  have hu : IsUnit (f₁ (integerModelTransition P h x)) := by
    rw [integerModelTransportHom_transition, ← hy₁ ()]
    exact (y₁ ()).isUnit
  refine ⟨A₁, hA₁, hs₁, h, inferInstance, hQ₁,
    IsLocalization.Away.liftAlgHom (integerModelTransition P h x) hu, ?_⟩
  intro b
  exact IsLocalization.Away.lift_eq (integerModelTransition P h x) hu b

end FLT.Mazur.Approximation
