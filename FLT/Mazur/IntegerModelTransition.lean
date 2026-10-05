/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialRelationIntegerModel

/-!
# Transition maps between coefficient models

For a fixed presentation, inclusion of coefficient rings induces a map of
quotient models. Its recovery map to the original algebra is unchanged.
No injectivity of a transition between quotient models is asserted.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
  {A₀ A₁ : Subalgebra ℤ A}

/-- Polynomial coefficient inclusions commute with the inclusion into the base. -/
theorem map_coefficient_inclusion (h : A₀ ≤ A₁) (p : MvPolynomial (Fin n) A₀) :
    map (algebraMap A₁ A) (map (Subalgebra.inclusion h).toRingHom p) =
      map (algebraMap A₀ A) p := by
  rw [map_map]
  rfl

variable [P.HasCoeffs A₀] [P.HasCoeffs A₁]

/-- The chosen relations in two coefficient rings agree under inclusion. -/
theorem map_relation_coefficient_inclusion (h : A₀ ≤ A₁) (j : Fin m) :
    map (Subalgebra.inclusion h).toRingHom (P.relationOfHasCoeffs A₀ j) =
      P.relationOfHasCoeffs A₁ j := by
  apply MvPolynomial.map_injective (f := algebraMap A₁ A) Subtype.val_injective
  rw [map_coefficient_inclusion, P.map_relationOfHasCoeffs, P.map_relationOfHasCoeffs]

/-- Enlargement of the coefficient ring gives a map of presentation models. -/
def integerModelTransition (h : A₀ ≤ A₁) :
    P.ModelOfHasCoeffs A₀ →+* P.ModelOfHasCoeffs A₁ :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (map (Subalgebra.inclusion h).toRingHom)) (by
      change Ideal.span _ ≤ RingHom.ker _
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      change Ideal.Quotient.mk _ (map (Subalgebra.inclusion h).toRingHom
        (P.relationOfHasCoeffs A₀ j)) = 0
      rw [map_relation_coefficient_inclusion]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩))

/-- Transition maps act by inclusion on polynomial representatives. -/
@[simp]
theorem integerModelTransition_mk (h : A₀ ≤ A₁) (p : MvPolynomial (Fin n) A₀) :
    integerModelTransition P h (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (map (Subalgebra.inclusion h).toRingHom p) := rfl

/-- Enlarging coefficients preserves the map recovering the original algebra. -/
theorem integerModelTransition_recovery (h : A₀ ≤ A₁) (b : P.ModelOfHasCoeffs A₀) :
    P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ integerModelTransition P h b) =
      P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b) := by
  induction b using Quotient.inductionOn' with | _ p => ?_
  change P.tensorModelOfHasCoeffsEquiv A₁
    (1 ⊗ₜ integerModelTransition P h (Ideal.Quotient.mk _ p)) =
      P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ Ideal.Quotient.mk _ p)
  simp only [integerModelTransition_mk, P.tensorModelOfHasCoeffsEquiv_tmul,
    map_one, one_mul]
  rw [← MvPolynomial.aeval_map_algebraMap A, map_coefficient_inclusion,
    MvPolynomial.aeval_map_algebraMap]

/-- Transition maps respect the coefficient inclusions. -/
@[simp]
theorem integerModelTransition_algebraMap (h : A₀ ≤ A₁) (a : A₀) :
    integerModelTransition P h (algebraMap A₀ (P.ModelOfHasCoeffs A₀) a) =
      algebraMap A₁ (P.ModelOfHasCoeffs A₁) (Subalgebra.inclusion h a) := by
  change Ideal.Quotient.mk _ (map (Subalgebra.inclusion h).toRingHom (C a)) = _
  rw [map_C]
  rfl

/-- Recovery of a coefficient agrees with its image in the original algebra. -/
@[simp]
theorem integerModelRecovery_algebraMap (a : A₀) :
    P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ algebraMap A₀ (P.ModelOfHasCoeffs A₀) a) =
      algebraMap A B (a : A) := by
  change P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ Ideal.Quotient.mk _ (C a)) = _
  rw [P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul, aeval_C]
  rfl

end FLT.Mazur.Approximation
