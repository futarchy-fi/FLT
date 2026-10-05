/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialRelationIntegerModel

/-!
# Simultaneous descent of relations in a finite affine family

Include coefficients of all ideal-membership witnesses in one stage. Every
lift of a prescribed vanishing polynomial then vanishes in its model. The
universal quantifier over lifts permits substitution and composition of maps.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.Approximation

universe u v w

/-- A finite family of presentations and finite families of vanishing
polynomials descend to one coefficient ring. Vanishing holds for any lift,
without requiring injectivity of the maps from the quotient models. -/
theorem exists_common_integer_relation_models {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] (B : ι → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : ι → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (κ : ι → Type w) [∀ i, Finite (κ i)]
    (q : ∀ i, κ i → MvPolynomial (Fin (n i)) A)
    (hq : ∀ i k, aeval (P i).val (q i k) = 0) (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ _hP : ∀ i, (P i).HasCoeffs A₀,
        ∀ i k (q₀ : MvPolynomial (Fin (n i)) A₀),
          map (algebraMap A₀ A) q₀ = q i k →
            (Ideal.Quotient.mk _ q₀ : (P i).ModelOfHasCoeffs A₀) = 0 := by
  classical
  have hw (i) (k : κ i) : ∃ c : Fin (m i) → MvPolynomial (Fin (n i)) A,
      ∑ j, c j * (P i).relation j = q i k := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [(P i).span_range_relation_eq_ker, (P i).ker_eq_ker_aeval_val]
    exact hq i k
  choose c hc using hw
  let t : Set A := s ∪ ⋃ i, ⋃ k, ⋃ j, (c i k j).coeffs
  have ht : t.Finite := hs.union (Set.finite_iUnion fun i ↦
    Set.finite_iUnion fun k ↦ Set.finite_iUnion fun j ↦ (c i k j).coeffs.finite_toSet)
  obtain ⟨A₀, hA₀, ht₀, hP⟩ := exists_common_integer_coefficients B n m P t ht
  let := hP
  have hl (i) (k : κ i) (j : Fin (m i)) :
      c i k j ∈ Set.range (map (algebraMap A₀ A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, ht₀ (Or.inr (Set.mem_iUnion.mpr ⟨i,
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨j, ha⟩⟩⟩))⟩, rfl⟩
  choose c₀ hc₀ using hl
  refine ⟨A₀, hA₀, fun a ha ↦ ht₀ (Or.inl ha), hP, fun i k q₀ hq₀ ↦ ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨c₀ i k, ?_⟩
  apply MvPolynomial.map_injective (f := algebraMap A₀ A) Subtype.val_injective
  simp only [map_sum, map_mul, (P i).map_relationOfHasCoeffs, hc₀, hq₀]
  exact hc i k

end FLT.Mazur.Approximation
