/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Integer models of finitely presented affine algebras

A finite family of finite presentations has a common finite-type integer
coefficient ring. Any prescribed finite set of base coefficients can be
included. Each model has an actual tensor-product identification with the
original algebra; no flatness of the coefficient-ring inclusion is needed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

variable {A : Type u} [CommRing A]

/-- A finite family of presentations can be realised over one finite-type integer
subalgebra, containing any prescribed finite set of base coefficients. -/
theorem exists_common_integer_coefficients {ι : Type v} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : ι → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∀ i, (P i).HasCoeffs A₀ := by
  let t : Set A := s ∪ ⋃ i, (P i).coeffs
  have ht : t.Finite := hs.union (Set.finite_iUnion fun i ↦ (P i).finite_coeffs)
  refine ⟨Algebra.adjoin ℤ t, Algebra.FiniteType.adjoin_of_finite ht,
    fun x hx ↦ Algebra.subset_adjoin (Or.inl hx), fun i ↦ ⟨?_⟩⟩
  intro x hx
  refine ⟨⟨x, Algebra.subset_adjoin (Or.inr ?_)⟩, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

/-- Finite families of finitely presented algebras descend simultaneously to a
finite-type integer subalgebra, with their base-change isomorphisms. -/
theorem exists_common_integer_models {ι : Type v} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Algebra.FinitePresentation A (B i)] (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∀ i, ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        Algebra.FinitePresentation A₀ B₀ ∧ Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B i) := by
  let P := fun i ↦ Algebra.Presentation.ofFinitePresentation A (B i)
  obtain ⟨A₀, hA₀, hs₀, hP⟩ := exists_common_integer_coefficients B _ _ P s hs
  refine ⟨A₀, hA₀, hs₀, fun i ↦ ?_⟩
  let := hP i
  exact ⟨(P i).ModelOfHasCoeffs A₀, inferInstance, inferInstance, inferInstance,
    ⟨(P i).tensorModelOfHasCoeffsEquiv A₀⟩⟩

/-- Every finitely presented algebra has an integer model, with a genuine
base-change identification and a finitely generated coefficient ring. -/
theorem exists_integer_model (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        Algebra.FinitePresentation A₀ B₀ ∧ Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B) := by
  obtain ⟨A₀, hA₀, _, h⟩ :=
    exists_common_integer_models (A := A) (fun _ : Unit ↦ B) ∅ Set.finite_empty
  exact ⟨A₀, hA₀, h ()⟩

end FLT.Mazur.Approximation
