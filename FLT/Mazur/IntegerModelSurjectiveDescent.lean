/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FixedModelElementLifts
public import FLT.Mazur.IntegerModelEventualEquality
public import FLT.Mazur.IntegerModelDiagramTransport
public import FLT.Mazur.PrincipalChartIntegerDescent

/-!
# Surjectivity descends to a coefficient model

Preimages of the finitely many target generators lift after enlargement.
Their equations then hold at a common later stage. Recovery maps need not
be injective or faithfully flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A fixed model map recovering a surjection becomes surjective after enlargement. -/
theorem exists_integer_model_surjective {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] C) (hφ : Function.Surjective φ)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        Function.Surjective (integerModelTransportHom P Q h f) := by
  classical
  choose b hb using fun i : Fin r ↦ hφ (Q.val i)
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, b₁, hb₁⟩ :=
    exists_fixed_model_element_lifts P A₀ b s hs
  let := hA₁
  let := hP₁
  let hQ₁ : Q.HasCoeffs A₁ := integerModel_hasCoeffs_mono Q h₀₁
  let f₁ := integerModelTransportHom P Q h₀₁ f
  let x₁ : Fin r → Q.ModelOfHasCoeffs A₁ := fun i ↦ Ideal.Quotient.mk _ (X i)
  let z := fun i ↦ f₁ (b₁ i) - x₁ i
  have hz (i) : Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ z i) = 0 := by
    change integerModelRecoveryHom Q (z i) = 0
    simp only [z, map_sub, integerModelRecoveryHom_apply]
    rw [integerModelTransportHom_recovery P Q h₀₁ f φ hf, hb₁, hb]
    simp [x₁, Q.tensorModelOfHasCoeffsEquiv_tmul]
  obtain ⟨S, hS, hsS, h₁S, hQS, hzS⟩ :=
    exists_integer_model_eventual_zero Q A₁ z hz s hs
  let := hQS
  let hPS : P.HasCoeffs S := integerModel_hasCoeffs_mono P h₁S
  let fS := integerModelTransportHom P Q h₁S f₁
  let bS := fun i ↦ integerModelTransition P h₁S (b₁ i)
  have hgen (i) : fS (bS i) = Ideal.Quotient.mk _ (X i) := by
    have hi := hzS i
    simpa only [z, map_sub, sub_eq_zero, x₁, integerModelTransition_mk, map_X,
      fS, bS, integerModelTransportHom_transition] using hi
  refine ⟨S, hS, hsS, h₀₁.trans h₁S, hPS, hQS, ?_⟩
  rw [← integerModelTransportHom_trans P Q h₀₁ h₁S]
  change Function.Surjective fS
  intro c
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨aeval bS p, ?_⟩
  rw [← AlgHom.comp_apply, comp_aeval]
  have he : aeval (fun i ↦ fS (bS i)) =
      (Ideal.Quotient.mkₐ S (Ideal.span (Set.range (Q.relationOfHasCoeffs S)))) := by
    ext i
    rw [aeval_X]
    exact hgen i
  exact AlgHom.congr_fun he p

end FLT.Mazur.Approximation
