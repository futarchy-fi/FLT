/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Linear assembly of finite original scalar numerators

Independent numerators in a compatible submodule give a single original
scalar and a linear lift of the free module of boundary generators. Relations
among those generators map into the exact boundary kernel; they are not
silently identified with zero.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.OriginalScalarFiniteLinearLifts
variable {R A B I : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B] [Finite I]
  (N : Submodule R A) (β : A →ₗ[R] B) (P : Ideal R) [P.IsPrime]

/-- Numerators in any compatible submodule have one original prime denominator. -/
theorem exists_common (t : I → B)
    (h : ∀ j, ∃ x : R, x ∉ P ∧ ∃ w : N, β w = x • t j) :
    ∃ x : R, x ∉ P ∧ ∃ w : I → N, ∀ j, β (w j) = x • t j := by
  classical
  let _ := Fintype.ofFinite I
  choose x hx w hw using h
  let x₀ : R := ∏ j, x j
  have hx₀ : x₀ ∉ P := by
    intro hm
    obtain ⟨j, _, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact hx j hj
  let y : I → R := fun j ↦ ∏ k ∈ Finset.univ.erase j, x k
  have hy (j : I) : y j * x j = x₀ :=
    Finset.prod_erase_mul Finset.univ x (Finset.mem_univ j)
  refine ⟨x₀, hx₀, fun j ↦ y j • w j, ?_⟩
  intro j
  change β (y j • (w j).val) = x₀ • t j
  rw [map_smul, hw, smul_smul, hy]

/-- The common numerator extends linearly to every formal combination of boundary generators. -/
theorem exists_linear_lift (t : I → B)
    (h : ∀ j, ∃ x : R, x ∉ P ∧ ∃ w : N, β w = x • t j) :
    ∃ x : R, x ∉ P ∧ ∃ L : (I →₀ R) →ₗ[R] N,
      (β.comp N.subtype).comp L = x • Finsupp.linearCombination R t := by
  obtain ⟨x, hx, w, hw⟩ := exists_common N β P t h
  refine ⟨x, hx, Finsupp.linearCombination R w, ?_⟩
  apply Finsupp.lhom_ext
  intro j r
  simp only [LinearMap.comp_apply, Finsupp.linearCombination_single,
    Submodule.subtype_apply, map_smul, hw,
    LinearMap.smul_apply]
  exact smul_comm r x (t j)

variable {N β}

omit [Finite I] in
/-- A single denominator works for the whole span, not only for the listed generators. -/
theorem span_lifts (t : I → B) (x : R) (L : (I →₀ R) →ₗ[R] N)
    (hL : (β.comp N.subtype).comp L = x • Finsupp.linearCombination R t)
    (b : B) (hb : b ∈ Submodule.span R (Set.range t)) :
    ∃ w : N, β w = x • b := by
  rw [← Finsupp.range_linearCombination] at hb
  obtain ⟨c, rfl⟩ := hb
  exact ⟨L c, LinearMap.congr_fun hL c⟩

omit [Finite I] in
/-- Relations between generators give exact boundary-zero compatible numerators. -/
theorem relation_maps_to_boundary_kernel (t : I → B) (x : R)
    (L : (I →₀ R) →ₗ[R] N)
    (hL : (β.comp N.subtype).comp L = x • Finsupp.linearCombination R t)
    (c : I →₀ R) (hc : Finsupp.linearCombination R t c = 0) :
    β (L c) = 0 := by
  have h := LinearMap.congr_fun hL c
  change β (L c) = x • Finsupp.linearCombination R t c at h
  simpa only [hc, smul_zero] using h

end FLT.Mazur.OriginalScalarFiniteLinearLifts
