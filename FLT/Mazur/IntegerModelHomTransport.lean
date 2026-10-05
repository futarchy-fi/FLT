/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelHomExtension

/-!
# Transporting maps between presentation models

Coefficient enlargement transports algebra maps and preserves their recovery
in the original algebras. In particular, enlarging a stage does not lose
comparison maps or equations already established there.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {n m r t : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin m))
  (Q : Algebra.Presentation A C (Fin r) (Fin t))
  {A₀ A₁ : Subalgebra ℤ A}

/-- Enlarging the coefficient subring retains all presentation coefficients. -/
theorem integerModel_hasCoeffs_mono (h : A₀ ≤ A₁) [P.HasCoeffs A₀] :
    P.HasCoeffs A₁ := by
  constructor
  intro a ha
  obtain ⟨b, rfl⟩ := P.coeffs_subset_range A₀ ha
  exact ⟨Subalgebra.inclusion h b, rfl⟩

variable [P.HasCoeffs A₀] [P.HasCoeffs A₁]

/-- Recover a model element as an algebra map over the coefficient ring. -/
def integerModelRecoveryHom : P.ModelOfHasCoeffs A₀ →ₐ[A₀] B where
  __ := (P.tensorModelOfHasCoeffsEquiv A₀).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom
  commutes' := integerModelRecovery_algebraMap P

/-- Recovery is evaluation of the scalar-extension equivalence on a pure tensor. -/
@[simp]
theorem integerModelRecoveryHom_apply (b : P.ModelOfHasCoeffs A₀) :
    integerModelRecoveryHom P b = P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b) := rfl

/-- Nested coefficient inclusions compose as the corresponding model maps. -/
theorem integerModelTransition_trans {A₂ : Subalgebra ℤ A} [P.HasCoeffs A₂]
    (h : A₀ ≤ A₁) (k : A₁ ≤ A₂) (b : P.ModelOfHasCoeffs A₀) :
    integerModelTransition P k (integerModelTransition P h b) =
      integerModelTransition P (h.trans k) b := by
  induction b using Quotient.inductionOn' with | _ p => ?_
  change Ideal.Quotient.mk _ (map (Subalgebra.inclusion k).toRingHom
    (map (Subalgebra.inclusion h).toRingHom p)) = _
  rw [map_map]
  rfl

variable [Q.HasCoeffs A₀] [Q.HasCoeffs A₁] (h : A₀ ≤ A₁)
  (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)

/-- Transport an algebra map to a larger common coefficient stage. -/
def integerModelTransportHom : P.ModelOfHasCoeffs A₁ →ₐ[A₁] Q.ModelOfHasCoeffs A₁ :=
  integerModelExtendHom P h ((integerModelTransition Q h).comp f.toRingHom) (by
    intro a
    change integerModelTransition Q h (f (algebraMap A₀ _ a)) = _
    rw [f.commutes, integerModelTransition_algebraMap])

/-- Transport commutes with the old source and target transition maps. -/
@[simp]
theorem integerModelTransportHom_transition (b : P.ModelOfHasCoeffs A₀) :
    integerModelTransportHom P Q h f (integerModelTransition P h b) =
      integerModelTransition Q h (f b) :=
  integerModelExtendHom_transition P h _ _ b

/-- The transported map recovers the same original algebra map. -/
theorem integerModelTransportHom_recovery (φ : B →ₐ[A] C)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (b : P.ModelOfHasCoeffs A₁) :
    Q.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ integerModelTransportHom P Q h f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ b)) := by
  have heq : (integerModelRecoveryHom Q).comp (integerModelTransportHom P Q h f) =
      (φ.restrictScalars A₁).comp (integerModelRecoveryHom P) := by
    apply integerModel_hom_ext P h
    intro x
    change Q.tensorModelOfHasCoeffsEquiv A₁
      (1 ⊗ₜ integerModelTransportHom P Q h f (integerModelTransition P h x)) =
        φ (P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ integerModelTransition P h x))
    rw [integerModelTransportHom_transition, integerModelTransition_recovery,
      integerModelTransition_recovery, hf]
  exact AlgHom.congr_fun heq b

end FLT.Mazur.Approximation
