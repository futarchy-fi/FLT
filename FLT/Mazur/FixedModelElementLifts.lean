/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelHomTransport

/-!
# Lifting finite element families into fixed presentation models

Enlarging a coefficient stage suffices to lift any finite family of elements.
The presentation is retained, so previously descended maps can be transported.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Lift finitely many elements while retaining a fixed presentation and initial stage. -/
theorem exists_fixed_model_element_lifts {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {n m : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    {I : Type v} [Finite I] (x : I → B) (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ _h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁,
        ∃ x₁ : I → P.ModelOfHasCoeffs A₁,
          ∀ i, P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ x₁ i) = x i := by
  classical
  obtain ⟨t, ht⟩ := A₀.fg_iff_finiteType.mpr inferInstance
  obtain ⟨A₁, hA₁, hs₁, p, hp⟩ :=
    exists_integer_polynomial_lifts (fun i ↦ P.σ (x i))
      (s ∪ t) (hs.union t.finite_toSet)
  have h : A₀ ≤ A₁ := by
    rw [← ht, Algebra.adjoin_le_iff]
    exact fun a ha ↦ hs₁ (Or.inr ha)
  let hP : P.HasCoeffs A₁ := integerModel_hasCoeffs_mono P h
  refine ⟨A₁, hA₁, fun a ha ↦ hs₁ (Or.inl ha), h, hP,
    fun i ↦ Ideal.Quotient.mk _ (p i), fun i ↦ ?_⟩
  rw [P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
    ← MvPolynomial.aeval_map_algebraMap A, hp, P.aeval_val_σ]

end FLT.Mazur.Approximation
