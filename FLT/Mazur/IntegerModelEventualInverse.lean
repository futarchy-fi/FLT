/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelEventualEquality
public import FLT.Mazur.IntegerModelHomTransport

/-!
# Inverse comparison maps at a finite coefficient stage

If two model maps recover inverse maps, one common enlargement makes them
actual inverses. The resulting equivalence retains both transition maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Two comparison maps which are inverse after recovery become an actual
algebra equivalence at a larger common stage. -/
theorem exists_integer_model_eventual_inverse {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (g : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] P.ModelOfHasCoeffs A₀)
    (hgf : ∀ b, P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g (f b)) =
      P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b))
    (hfg : ∀ c, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f (g c)) =
      Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁, ∃ _hQ : Q.HasCoeffs A₁,
        ∃ e : P.ModelOfHasCoeffs A₁ ≃ₐ[A₁] Q.ModelOfHasCoeffs A₁,
          (∀ b, e (integerModelTransition P h b) = integerModelTransition Q h (f b)) ∧
          ∀ c, e.symm (integerModelTransition Q h c) = integerModelTransition P h (g c) := by
  let : Algebra.FiniteType ℤ (P.ModelOfHasCoeffs A₀) :=
    Algebra.FiniteType.trans (R := ℤ) (S := A₀) inferInstance inferInstance
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, heqP⟩ :=
    exists_integer_model_eventual_hom_eq P A₀ (g.comp f).toRingHom
      (RingHom.id _) hgf s hs
  let := hA₁
  let := hP₁
  let : Q.HasCoeffs A₁ := integerModel_hasCoeffs_mono Q h₀₁
  let f₁ := integerModelTransportHom P Q h₀₁ f
  let g₁ := integerModelTransportHom Q P h₀₁ g
  have hrec : (integerModelRecoveryHom Q).comp (f₁.comp g₁) =
      integerModelRecoveryHom Q := by
    apply integerModel_hom_ext Q h₀₁
    intro c
    change Q.tensorModelOfHasCoeffsEquiv A₁
      (1 ⊗ₜ f₁ (g₁ (integerModelTransition Q h₀₁ c))) =
        Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ integerModelTransition Q h₀₁ c)
    rw [integerModelTransportHom_transition, integerModelTransportHom_transition,
      integerModelTransition_recovery, integerModelTransition_recovery, hfg]
  let : Algebra.FiniteType ℤ (Q.ModelOfHasCoeffs A₁) :=
    Algebra.FiniteType.trans (R := ℤ) (S := A₁) inferInstance inferInstance
  obtain ⟨A₂, hA₂, hs₂, h₁₂, hQ₂, heqQ⟩ :=
    exists_integer_model_eventual_hom_eq Q A₁ (f₁.comp g₁).toRingHom
      (RingHom.id _) (fun c ↦ AlgHom.congr_fun hrec c) s hs
  let := hQ₂
  let : P.HasCoeffs A₂ := integerModel_hasCoeffs_mono P h₁₂
  let f₂ := integerModelTransportHom P Q h₁₂ f₁
  let g₂ := integerModelTransportHom Q P h₁₂ g₁
  have hgf₂ : g₂.comp f₂ = AlgHom.id A₂ _ := by
    apply integerModel_hom_ext P (h₀₁.trans h₁₂)
    intro b
    change g₂ (f₂ (integerModelTransition P (h₀₁.trans h₁₂) b)) =
      integerModelTransition P (h₀₁.trans h₁₂) b
    rw [← integerModelTransition_trans P h₀₁ h₁₂,
      integerModelTransportHom_transition, integerModelTransportHom_transition,
      integerModelTransportHom_transition, integerModelTransportHom_transition]
    exact congrArg (integerModelTransition P h₁₂) (RingHom.congr_fun heqP b)
  have hfg₂ : f₂.comp g₂ = AlgHom.id A₂ _ := by
    apply integerModel_hom_ext Q h₁₂
    intro c
    change f₂ (g₂ (integerModelTransition Q h₁₂ c)) = integerModelTransition Q h₁₂ c
    rw [integerModelTransportHom_transition, integerModelTransportHom_transition]
    exact RingHom.congr_fun heqQ c
  refine ⟨A₂, hA₂, hs₂, h₀₁.trans h₁₂, inferInstance, hQ₂,
    AlgEquiv.ofAlgHom f₂ g₂ hfg₂ hgf₂, ?_, ?_⟩
  · intro b
    change f₂ (integerModelTransition P (h₀₁.trans h₁₂) b) = _
    rw [← integerModelTransition_trans P h₀₁ h₁₂,
      integerModelTransportHom_transition, integerModelTransportHom_transition,
      integerModelTransition_trans]
  · intro c
    change g₂ (integerModelTransition Q (h₀₁.trans h₁₂) c) = _
    rw [← integerModelTransition_trans Q h₀₁ h₁₂,
      integerModelTransportHom_transition, integerModelTransportHom_transition,
      integerModelTransition_trans]

end FLT.Mazur.Approximation
