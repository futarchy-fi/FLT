/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentationIntegerModel

/-!
# Descending polynomial relations to integer models

A polynomial that vanishes in an algebra need not vanish in an arbitrary
coefficient model. We include the coefficients of ideal-membership witnesses
as well as those of the polynomial. This descends finitely many equalities
without assuming the map from the coefficient model is injective.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.Approximation

universe u v w

variable {A : Type u} [CommRing A]

/-- Finitely many polynomials can be lifted to a finite-type integer subalgebra
containing any specified finite set of coefficients. -/
theorem exists_integer_polynomial_lifts {ι : Type v} {κ : Type w} [Finite κ]
    (q : κ → MvPolynomial ι A) (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ q₀ : κ → MvPolynomial ι A₀, ∀ k, map (algebraMap A₀ A) (q₀ k) = q k := by
  let t : Set A := s ∪ ⋃ k, (q k).coeffs
  have ht : t.Finite := hs.union (Set.finite_iUnion fun k ↦ (q k).coeffs.finite_toSet)
  let A₀ := Algebra.adjoin ℤ t
  have hl (k) : q k ∈ Set.range (map (algebraMap A₀ A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro x hx
    exact ⟨⟨x, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.mpr ⟨k, hx⟩))⟩, rfl⟩
  choose q₀ hq₀ using hl
  exact ⟨A₀, Algebra.FiniteType.adjoin_of_finite ht,
    fun x hx ↦ Algebra.subset_adjoin (Or.inl hx), q₀, hq₀⟩

/-- Vanishing of finitely many polynomials descends after including the
coefficients of their ideal-membership witnesses in the finite stage. -/
theorem exists_integer_model_relations {B : Type u} [CommRing B] [Algebra A B]
    {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    {κ : Type v} [Finite κ] (q : κ → MvPolynomial (Fin n) A)
    (hq : ∀ k, aeval P.val (q k) = 0) (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ hP : P.HasCoeffs A₀, ∃ q₀ : κ → MvPolynomial (Fin n) A₀,
        (∀ k, map (algebraMap A₀ A) (q₀ k) = q k) ∧
          ∀ k, q₀ k ∈ Ideal.span (Set.range (@Algebra.Presentation.relationOfHasCoeffs
            _ _ _ _ _ _ _ P A₀ _ _ _ _ hP)) := by
  classical
  have hw (k) : ∃ c : Fin m → MvPolynomial (Fin n) A,
      ∑ j, c j * P.relation j = q k := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val]
    exact hq k
  choose c hc using hw
  let r : κ ⊕ (κ × Fin m) → MvPolynomial (Fin n) A :=
    Sum.elim q (fun kj ↦ c kj.1 kj.2)
  obtain ⟨A₀, hA₀, hs₀, r₀, hr₀⟩ :=
    exists_integer_polynomial_lifts r (s ∪ P.coeffs) (hs.union P.finite_coeffs)
  have hP : P.HasCoeffs A₀ := ⟨fun x hx ↦ ⟨⟨x, hs₀ (Or.inr hx)⟩, rfl⟩⟩
  let := hP
  refine ⟨A₀, hA₀, fun x hx ↦ hs₀ (Or.inl hx), hP, fun k ↦ r₀ (.inl k),
    fun k ↦ hr₀ (.inl k), fun k ↦ ?_⟩
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨fun j ↦ r₀ (.inr (k, j)), ?_⟩
  apply MvPolynomial.map_injective (f := algebraMap A₀ A) Subtype.val_injective
  simp only [map_sum, map_mul, P.map_relationOfHasCoeffs, hr₀]
  exact hc k

end FLT.Mazur.Approximation
