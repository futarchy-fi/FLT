/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelEventualInverse
public import FLT.Mazur.ScalarCompatibleIntegerModel

/-!
# Descending the invertibility of a model map

A model map recovering an isomorphism becomes an isomorphism after a
coefficient enlargement. The inverse is lifted and both inverse equations
are proved at a common stage; no inverse at the old stage is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- If a fixed model map recovers an algebra equivalence, some later model
has an equivalence extending that map and recovering the given equivalence. -/
theorem exists_integer_model_isomorphism {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (e : B ≃ₐ[A] C)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      e (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (s : Set A) (hs : s.Finite) :
    ∃ A₂ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₂ ∧ s ⊆ A₂ ∧
      ∃ h : A₀ ≤ A₂, ∃ _hP : P.HasCoeffs A₂, ∃ _hQ : Q.HasCoeffs A₂,
        ∃ e₂ : P.ModelOfHasCoeffs A₂ ≃ₐ[A₂] Q.ModelOfHasCoeffs A₂,
          (∀ b, e₂ (integerModelTransition P h b) = integerModelTransition Q h (f b)) ∧
          ∀ b, Q.tensorModelOfHasCoeffsEquiv A₂ (1 ⊗ₜ e₂ b) =
            e (P.tensorModelOfHasCoeffsEquiv A₂ (1 ⊗ₜ b)) := by
  let : Algebra.FiniteType ℤ (Q.ModelOfHasCoeffs A₀) :=
    Algebra.FiniteType.trans (R := ℤ) (S := A₀) inferInstance inferInstance
  let ψ := e.symm.toRingHom.comp (integerModelRecoveryHom Q (A₀ := A₀)).toRingHom
  have hψ (a : A₀) : ψ (algebraMap A₀ (Q.ModelOfHasCoeffs A₀) a) =
      algebraMap A B (a : A) := by
    change e.symm (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ algebraMap A₀ _ a)) = _
    rw [integerModelRecovery_algebraMap, e.symm.commutes]
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, g, hg, hscalar⟩ :=
    exists_scalar_compatible_integer_model_hom P A₀ ψ hψ s hs
  let := hA₁
  let := hP₁
  let : Q.HasCoeffs A₁ := integerModel_hasCoeffs_mono Q h₀₁
  let f₁ := integerModelTransportHom P Q h₀₁ f
  let g₁ := integerModelExtendHom Q h₀₁ g hscalar
  have hf₁ (b) : Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ f₁ b) =
      e (P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ b)) :=
    integerModelTransportHom_recovery P Q h₀₁ f e.toAlgHom hf b
  have hg₁ (c) : P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ g₁ c) =
      e.symm (Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ c)) := by
    have heq : (integerModelRecoveryHom P).comp g₁ =
        (e.symm.toAlgHom.restrictScalars A₁).comp (integerModelRecoveryHom Q) := by
      apply integerModel_hom_ext Q h₀₁
      intro c₀
      change P.tensorModelOfHasCoeffsEquiv A₁
        (1 ⊗ₜ g₁ (integerModelTransition Q h₀₁ c₀)) =
          e.symm (Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ integerModelTransition Q h₀₁ c₀))
      rw [integerModelExtendHom_transition, integerModelTransition_recovery, hg]
      rfl
    exact AlgHom.congr_fun heq c
  have hgf (b) : P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ g₁ (f₁ b)) =
      P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ b) := by
    rw [hg₁, hf₁, e.symm_apply_apply]
  have hfg (c) : Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ f₁ (g₁ c)) =
      Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ c) := by
    rw [hf₁, hg₁, e.apply_symm_apply]
  obtain ⟨A₂, hA₂, hs₂, h₁₂, hP₂, hQ₂, e₂, he₂, _⟩ :=
    exists_integer_model_eventual_inverse P Q A₁ f₁ g₁ hgf hfg s hs
  let := hP₂
  let := hQ₂
  have hext : e₂.toAlgHom = integerModelTransportHom P Q h₁₂ f₁ := by
    apply integerModel_hom_ext P h₁₂
    intro b
    exact (he₂ b).trans (integerModelTransportHom_transition P Q h₁₂ f₁ b).symm
  refine ⟨A₂, hA₂, hs₂, h₀₁.trans h₁₂, hP₂, hQ₂, e₂, ?_, ?_⟩
  · intro b
    rw [← integerModelTransition_trans P h₀₁ h₁₂, he₂,
      integerModelTransportHom_transition, integerModelTransition_trans]
  · intro b
    change Q.tensorModelOfHasCoeffsEquiv A₂ (1 ⊗ₜ e₂.toAlgHom b) = _
    rw [hext]
    exact integerModelTransportHom_recovery P Q h₁₂ f₁ e.toAlgHom hf₁ b

end FLT.Mazur.Approximation
