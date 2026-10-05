/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FixedTargetIntegerModel
public import FLT.Mazur.IntegerModelEventualEquality

/-!
# Scalar-compatible lifts to larger integer models

After lifting a map to a fixed target presentation, its two restrictions
to the old coefficient ring agree after recovery. Eventual equality makes
them agree at a larger stage, giving a lift that respects the old scalars.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A scalar-compatible map lifts to a later model with scalar compatibility
already valid there, not merely after extending scalars to the original base. -/
theorem exists_scalar_compatible_integer_model_hom {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [Algebra A₀ C] [Algebra.FiniteType ℤ C]
    (φ : C →+* B)
    (hφ : ∀ a : A₀, φ (algebraMap A₀ C a) = algebraMap A B (a : A))
    (s : Set A) (hs : s.Finite) :
    ∃ A₂ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₂ ∧ s ⊆ A₂ ∧
      ∃ h : A₀ ≤ A₂, ∃ _hP : P.HasCoeffs A₂,
        ∃ φ₂ : C →+* P.ModelOfHasCoeffs A₂,
          (∀ c, P.tensorModelOfHasCoeffsEquiv A₂ (1 ⊗ₜ φ₂ c) = φ c) ∧
          ∀ a : A₀, φ₂ (algebraMap A₀ C a) =
            algebraMap A₂ (P.ModelOfHasCoeffs A₂) (Subalgebra.inclusion h a) := by
  obtain ⟨A₁, hA₁, _, h₀₁, hP₁, f, hf⟩ :=
    exists_fixed_target_integer_model_hom P A₀ φ s hs
  let := hA₁
  let := hP₁
  let g : A₀ →+* P.ModelOfHasCoeffs A₁ :=
    (algebraMap A₁ (P.ModelOfHasCoeffs A₁)).comp (Subalgebra.inclusion h₀₁).toRingHom
  have hfg (a : A₀) :
      P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ (f.comp (algebraMap A₀ C)) a) =
        P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ g a) := by
    change P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ f (algebraMap A₀ C a)) =
      P.tensorModelOfHasCoeffsEquiv A₁
        (1 ⊗ₜ algebraMap A₁ (P.ModelOfHasCoeffs A₁) (Subalgebra.inclusion h₀₁ a))
    rw [hf, hφ, integerModelRecovery_algebraMap]
    rfl
  obtain ⟨A₂, hA₂, hs₂, h₁₂, hP₂, heq⟩ :=
    exists_integer_model_eventual_hom_eq P A₁ (f.comp (algebraMap A₀ C)) g hfg s hs
  let := hP₂
  refine ⟨A₂, hA₂, hs₂, h₀₁.trans h₁₂, hP₂,
    (integerModelTransition P h₁₂).comp f, ?_, ?_⟩
  · intro c
    change P.tensorModelOfHasCoeffsEquiv A₂ (1 ⊗ₜ integerModelTransition P h₁₂ (f c)) = _
    rw [integerModelTransition_recovery, hf]
  · intro a
    have ha := RingHom.congr_fun heq a
    change integerModelTransition P h₁₂ (f (algebraMap A₀ C a)) =
      integerModelTransition P h₁₂
        (algebraMap A₁ (P.ModelOfHasCoeffs A₁) (Subalgebra.inclusion h₀₁ a)) at ha
    rw [integerModelTransition_algebraMap] at ha
    exact ha

end FLT.Mazur.Approximation
