/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteErrorReductionFrame

/-!
# Constructing all approximation orders from one-step reductions

Each correction reduces the error by one power of the ideal while keeping it
inside the same error module. No completeness, compatibility hypothesis, or
Noetherian hypothesis is used to construct the approximations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N) (I : Ideal R) (E : Submodule R N)
  (h : ∀ y ∈ E, ∃ z : M, y - F z ∈ I • E)
include h

/-- A generator reduction increases the ideal order of any error in the fixed module. -/
theorem power_reduction (n : ℕ) (y : N) (hy : y ∈ I ^ n • E) :
    ∃ z : M, y - F z ∈ I ^ (n + 1) • E := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro a ha x hx
    obtain ⟨z, hz⟩ := h x hx
    refine ⟨a • z, ?_⟩
    rw [map_smul, ← smul_sub]
    have he := Submodule.smul_mem_smul ha hz
    simpa only [pow_succ, mul_smul] using he
  · intro x y hx hy
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    refine ⟨z + w, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hz hw

/-- One initial error and one-step reduction construct full approximations at every order. -/
theorem exists_approximations (y : N) (z₀ : M) (hy : y - F z₀ ∈ E) :
    ∀ n : ℕ, ∃ z : M, y - F z ∈ I ^ n • E := by
  intro n
  induction n with
  | zero => exact ⟨z₀, by simpa using hy⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := power_reduction F I E h n _ hz
    refine ⟨z + w, ?_⟩
    rwa [map_add, ← sub_sub]

omit h E in
/-- A finite reduction matrix constructs the uniform finite module and every approximation. -/
theorem exists_approximations_of_matrix {κ : Type*} [Fintype κ]
    (e : κ → N) (v : κ → M) (c : κ → κ → R)
    (hc : ∀ j k, c j k ∈ I)
    (he : ∀ j, e j - F (v j) = ∑ k, c j k • e k)
    (y : N) (z₀ : M) (b : κ → R) (hy : y - F z₀ = ∑ j, b j • e j) :
    ∃ E : Submodule R N, E.FG ∧ ∀ n : ℕ, ∃ z : M, y - F z ∈ I ^ n • E := by
  refine ⟨Submodule.span R (Set.range e), Submodule.fg_span (Set.finite_range e), ?_⟩
  apply exists_approximations F I _ (reduction_of_matrix F I e v c hc he) y z₀
  rw [hy]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end FLT.Mazur.FiniteErrorReduction
