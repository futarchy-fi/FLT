/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# A common original scalar for finitely many full-relation lifts

Multiply the separately constructed original denominators. Each numerator is
rescaled by the product of all the other denominators. Boundary values and
full relation equations are preserved, without requiring a common usable open.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.OriginalScalarFiniteRelationNumerators
variable {R A B C I : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Finite I] (σ : R →+* A) (β : A →+* B) (F H : A →+* C)
  (hσ : ∀ x, F (σ x) = H (σ x)) (P : Ideal R) [P.IsPrime]

include hσ in
/-- Finite independent full-relation numerators have a common original prime denominator. -/
theorem exists_common_numerator (t : I → B)
    (h : ∀ j, ∃ x : R, x ∉ P ∧ ∃ w : A,
      β w = β (σ x) * t j ∧ F w = H w) :
    ∃ x : R, x ∉ P ∧ ∃ w : I → A,
      ∀ j, β (w j) = β (σ x) * t j ∧ F (w j) = H (w j) := by
  classical
  let _ := Fintype.ofFinite I
  choose x hx w hw he using h
  let x₀ : R := ∏ j, x j
  have hx₀ : x₀ ∉ P := by
    intro hm
    obtain ⟨j, _, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact hx j hj
  let y : I → R := fun j ↦ ∏ k ∈ Finset.univ.erase j, x k
  have hy (j : I) : y j * x j = x₀ :=
    Finset.prod_erase_mul Finset.univ x (Finset.mem_univ j)
  refine ⟨x₀, hx₀, fun j ↦ σ (y j) * w j, ?_⟩
  intro j
  constructor
  · rw [map_mul, hw j, ← mul_assoc, ← map_mul, ← map_mul, hy j]
  · rw [map_mul, map_mul, hσ, he j]

end FLT.Mazur.OriginalScalarFiniteRelationNumerators
