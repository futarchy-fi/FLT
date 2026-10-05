/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalChartOpenImmersion
public import FLT.Mazur.PrincipalComparisonIntegerModel

/-!
# Descending a principal chart from its fixed model map

A model map recovering the canonical map to a principal localization becomes
an open immersion after enlarging coefficients. Invertibility of the marked
image and the localization factorization are constructed, not assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Transport of model maps is compatible with composition of coefficient inclusions. -/
theorem integerModelTransportHom_trans {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    {A₀ A₁ A₂ : Subalgebra ℤ A}
    [P.HasCoeffs A₀] [P.HasCoeffs A₁] [P.HasCoeffs A₂]
    [Q.HasCoeffs A₀] [Q.HasCoeffs A₁] [Q.HasCoeffs A₂]
    (h : A₀ ≤ A₁) (k : A₁ ≤ A₂)
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀) :
    integerModelTransportHom P Q k (integerModelTransportHom P Q h f) =
      integerModelTransportHom P Q (h.trans k) f := by
  apply integerModel_hom_ext P (h.trans k)
  intro b
  rw [← integerModelTransition_trans P h k,
    integerModelTransportHom_transition, integerModelTransportHom_transition,
    integerModelTransition_trans Q h k, integerModelTransition_trans P h k,
    integerModelTransportHom_transition]

/-- A fixed model map recovering a principal chart eventually induces an open immersion. -/
theorem exists_integer_model_principal_chart {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    (x : P.ModelOfHasCoeffs A₀)
    (Q : Algebra.Presentation A
      (Localization.Away (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x))) (Fin r) (Fin t))
    [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ A₂ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₂ ∧ s ⊆ A₂ ∧
      ∃ h : A₀ ≤ A₂, ∃ _hP : P.HasCoeffs A₂, ∃ _hQ : Q.HasCoeffs A₂,
        IsOpenImmersion (Spec.map
          (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom)) := by
  let z := P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x)
  obtain ⟨y, hy⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away z) z
  have hunit : Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f x) = (y : Localization.Away z) := by
    rw [hf]
    exact hy.symm
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, hQ₁, F, hF⟩ :=
    exists_integer_model_principal_comparison P Q A₀ f x y hunit s hs
  let := hA₁
  let := hP₁
  let := hQ₁
  let f₁ := integerModelTransportHom P Q h₀₁ f
  have hf₁ (b) : Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ f₁ b) =
      algebraMap B _ (P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ b)) :=
    integerModelTransportHom_recovery P Q h₀₁ f
      (IsScalarTower.toAlgHom A B (Localization.Away z)) hf b
  obtain ⟨A₂, hA₂, hs₂, h₁₂, hP₂, hQ₂, hopen⟩ :=
    exists_integer_model_principal_openImmersion_of_eq P A₁
      (integerModelTransition P h₀₁ x) z (integerModelTransition_recovery P h₀₁ x)
      Q F f₁ hF hf₁ s hs
  let := hP₂
  let := hQ₂
  refine ⟨A₂, hA₂, hs₂, h₀₁.trans h₁₂, hP₂, hQ₂, ?_⟩
  simpa only [f₁, integerModelTransportHom_trans] using hopen

end FLT.Mazur.Approximation
