/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteErrorReduction
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite error frames and finite reduction matrices

Only one correcting vector per generator and a matrix with entries in the
error ideal are needed. The common finite error module is constructed as the
span of this fixed frame, rather than inferred from separate approximation orders.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N κ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N) (I : Ideal R) (e : κ → N)

/-- Correcting generators modulo their ideal-weighted span corrects every element of the span. -/
theorem reduction_of_generators
    (h : ∀ j, ∃ z : M, e j - F z ∈ I • Submodule.span R (Set.range e)) :
    ∀ y ∈ Submodule.span R (Set.range e),
      ∃ z : M, y - F z ∈ I • Submodule.span R (Set.range e) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    refine ⟨z + w, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hz hw
  | smul a x _ hx =>
    obtain ⟨z, hz⟩ := hx
    refine ⟨a • z, ?_⟩
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hz

variable [Fintype κ]

/-- A finite matrix in the ideal gives every generator's one-step reduction. -/
theorem reduction_of_matrix (v : κ → M) (c : κ → κ → R)
    (hc : ∀ j k, c j k ∈ I)
    (he : ∀ j, e j - F (v j) = ∑ k, c j k • e k) :
    ∀ y ∈ Submodule.span R (Set.range e),
      ∃ z : M, y - F z ∈ I • Submodule.span R (Set.range e) := by
  apply reduction_of_generators F I e
  intro j
  refine ⟨v j, ?_⟩
  rw [he]
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem_smul (hc j k) (Submodule.subset_span ⟨k, rfl⟩)

/-- Finite generator reductions construct one multiplier valid for the entire fixed frame. -/
theorem exists_frame_multiplier (v : κ → M) (c : κ → κ → R)
    (hc : ∀ j k, c j k ∈ I)
    (he : ∀ j, e j - F (v j) = ∑ k, c j k • e k) :
    ∃ a : R, a - 1 ∈ I ∧
      ∀ y ∈ Submodule.span R (Set.range e), ∃ z : M, F z = a • y :=
  exists_common_multiplier F I _ (Submodule.fg_span (Set.finite_range e))
    (reduction_of_matrix F I e v c hc he)

/-- A finite initial error expression and reduction matrix construct a scaled exact preimage. -/
theorem exists_lift_of_matrix (v : κ → M) (c : κ → κ → R)
    (hc : ∀ j k, c j k ∈ I)
    (he : ∀ j, e j - F (v j) = ∑ k, c j k • e k)
    (y : N) (z₀ : M) (b : κ → R) (hy : y - F z₀ = ∑ j, b j • e j) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ F z = a • y := by
  apply exists_scaled_lift F I _ (Submodule.fg_span (Set.finite_range e))
    (reduction_of_matrix F I e v c hc he) y z₀
  rw [hy]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end FLT.Mazur.FiniteErrorReduction
