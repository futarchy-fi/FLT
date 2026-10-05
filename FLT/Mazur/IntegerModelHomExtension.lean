/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelTransition

/-!
# Extending maps from coefficient models

A map from an old presentation model to an algebra over a larger coefficient
ring extends uniquely if it respects the old scalars. This supplies the
universal property needed to transport comparison maps during descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial

namespace FLT.Mazur.Approximation

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
  {A₀ A₁ : Subalgebra ℤ A} [P.HasCoeffs A₀] [P.HasCoeffs A₁]
  (h : A₀ ≤ A₁) {D : Type u} [CommRing D] [Algebra A₁ D]
  (f : P.ModelOfHasCoeffs A₀ →+* D)
  (hf : ∀ a : A₀, f (algebraMap A₀ (P.ModelOfHasCoeffs A₀) a) =
    algebraMap A₁ D (Subalgebra.inclusion h a))

omit [P.HasCoeffs A₁] in
include hf in
/-- Evaluating a polynomial after coefficient inclusion agrees with applying
an old scalar-compatible map to its quotient class. -/
theorem integerModel_eval_map (p : MvPolynomial (Fin n) A₀) :
    aeval (fun i ↦ f (Ideal.Quotient.mk _ (X i)))
      (map (Subalgebra.inclusion h).toRingHom p) = f (Ideal.Quotient.mk _ p) := by
  have heq : (aeval (fun i ↦ f (Ideal.Quotient.mk _ (X i)))).toRingHom.comp
      (map (Subalgebra.inclusion h).toRingHom) = f.comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change aeval _ (map (Subalgebra.inclusion h).toRingHom (C a)) = _
      rw [map_C, aeval_C]
      exact (hf a).symm
    · intro i
      change aeval _ (map (Subalgebra.inclusion h).toRingHom (X i)) = _
      rw [map_X, aeval_X]
      rfl
  exact RingHom.congr_fun heq p

/-- Extend a scalar-compatible map from an old model to the enlarged model. -/
def integerModelExtendHom : P.ModelOfHasCoeffs A₁ →ₐ[A₁] D :=
  Ideal.Quotient.liftₐ _ (aeval (fun i ↦ f (Ideal.Quotient.mk _ (X i)))) (by
    change Ideal.span _ ≤ RingHom.ker _
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    change aeval (fun i ↦ f (Ideal.Quotient.mk _ (X i)))
      (P.relationOfHasCoeffs A₁ j) = 0
    rw [← map_relation_coefficient_inclusion P h,
      integerModel_eval_map P h f hf]
    have hz : (Ideal.Quotient.mk _ (P.relationOfHasCoeffs A₀ j) :
        P.ModelOfHasCoeffs A₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
    rw [hz, map_zero])

/-- The extension preserves values on every element of the old model. -/
@[simp]
theorem integerModelExtendHom_transition (b : P.ModelOfHasCoeffs A₀) :
    integerModelExtendHom P h f hf (integerModelTransition P h b) = f b := by
  induction b using Quotient.inductionOn' with | _ p => ?_
  change aeval (fun i ↦ f (Ideal.Quotient.mk _ (X i)))
    (map (Subalgebra.inclusion h).toRingHom p) = f (Ideal.Quotient.mk _ p)
  exact integerModel_eval_map P h f hf p

/-- Algebra maps out of the enlarged model are determined by the old model. -/
theorem integerModel_hom_ext (g k : P.ModelOfHasCoeffs A₁ →ₐ[A₁] D)
    (hgk : ∀ b, g (integerModelTransition P h b) = k (integerModelTransition P h b)) :
    g = k := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change g (Ideal.Quotient.mk _ (X i)) = k (Ideal.Quotient.mk _ (X i))
  simpa only [integerModelTransition_mk, map_X] using hgk (Ideal.Quotient.mk _ (X i))

/-- The extension is the unique algebra map with the specified old values. -/
theorem integerModelExtendHom_unique (g : P.ModelOfHasCoeffs A₁ →ₐ[A₁] D)
    (hg : ∀ b, g (integerModelTransition P h b) = f b) :
    g = integerModelExtendHom P h f hf := by
  apply integerModel_hom_ext P h
  intro b
  rw [hg, integerModelExtendHom_transition]

end FLT.Mazur.Approximation
