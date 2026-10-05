/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelHomTransport

/-!
# Units in a fixed coefficient model

Elements of a fixed model which recover units become units after one
common enlargement. The new units have exactly the transitioned old
values, so they can be used to extend fixed maps through localizations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Finitely many recovered units become units without replacing the fixed
presentation or changing the transitioned values of the marked elements. -/
theorem exists_integer_model_eventual_units {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {n m : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    {K : Type v} [Finite K] (b : K → P.ModelOfHasCoeffs A₀) (x : K → Bˣ)
    (hb : ∀ k, P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b k) = (x k : B))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁,
        ∃ x₁ : K → (P.ModelOfHasCoeffs A₁)ˣ,
          ∀ k, (x₁ k : P.ModelOfHasCoeffs A₁) = integerModelTransition P h (b k) := by
  classical
  obtain ⟨t, ht⟩ := A₀.fg_iff_finiteType.mpr inferInstance
  have hl (k) : ∃ p : MvPolynomial (Fin n) A₀, Ideal.Quotient.mk _ p = b k :=
    Ideal.Quotient.mk_surjective (b k)
  choose p hp using hl
  let v := fun k ↦ P.σ ((x k)⁻¹ : Bˣ)
  let q := fun k ↦ map (algebraMap A₀ A) (p k) * v k - 1
  have hq (k) : aeval P.val (q k) = 0 := by
    have hk := hb k
    rw [← hp k, P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul] at hk
    simp [q, MvPolynomial.aeval_map_algebraMap, hk, v]
  let S : Set A := (s ∪ t) ∪ ⋃ k, (v k).coeffs
  have hS : S.Finite := (hs.union t.finite_toSet).union
    (Set.finite_iUnion fun k ↦ (v k).coeffs.finite_toSet)
  obtain ⟨A₁, hA₁, hS₁, hP₁, q₁, hq₁, hz⟩ :=
    exists_integer_model_relations P q hq S hS
  let := hP₁
  have h : A₀ ≤ A₁ := by
    rw [← ht, Algebra.adjoin_le_iff]
    exact fun a ha ↦ hS₁ (Or.inl (Or.inr ha))
  have hv (k) : v k ∈ Set.range (map (algebraMap A₁ A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, hS₁ (Or.inr (Set.mem_iUnion.mpr ⟨k, ha⟩))⟩, rfl⟩
  choose v₁ hv₁ using hv
  let π := Ideal.Quotient.mkₐ A₁ (Ideal.span (Set.range (P.relationOfHasCoeffs A₁)))
  have hinv (k) : integerModelTransition P h (b k) * π (v₁ k) = 1 := by
    have heq : map (Subalgebra.inclusion h).toRingHom (p k) * v₁ k - 1 = q₁ k := by
      apply MvPolynomial.map_injective (f := algebraMap A₁ A) Subtype.val_injective
      rw [map_sub, map_mul, map_one, map_coefficient_inclusion, hv₁, hq₁]
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr (hz k)
    rw [← heq] at he
    change π (map (Subalgebra.inclusion h).toRingHom (p k) * v₁ k - 1) = 0 at he
    rw [map_sub, map_mul, map_one, sub_eq_zero] at he
    rw [← hp k, integerModelTransition_mk]
    exact he
  exact ⟨A₁, hA₁, fun a ha ↦ hS₁ (Or.inl (Or.inl ha)), h, hP₁,
    fun k ↦ ⟨integerModelTransition P h (b k), π (v₁ k), hinv k,
      (mul_comm _ _).trans (hinv k)⟩, fun _ ↦ rfl⟩

end FLT.Mazur.Approximation
