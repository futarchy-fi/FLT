/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteErrorReductionIteration
public import Mathlib.LinearAlgebra.Prod

/-!
# Kernel pairs constructed by finite error reduction

A fixed finite frame of full equation errors, one reducing correction per
generator, and one initial pair produce both all-order approximations and an
exact pair. The exact multiplier is congruent to one without Noetherianity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (D : (R × M) →ₗ[R] N)

/-- The full equation of a pair is its scalar error minus the correction image. -/
theorem pair_difference (a : R) (z : M) :
    D (a, -z) = a • D (1, 0) - (D.comp (LinearMap.inr R R M)) z := by
  calc
    D (a, -z) = D (a • (1, 0) - (0, z)) := by
      congr 1
      ext <;> simp
    _ = _ := by rw [map_sub, map_smul]; rfl

variable (I : Ideal R) {κ : Type*} [Fintype κ]
  (e : κ → N) (v : κ → M) (c : κ → κ → R)
  (hc : ∀ j k, c j k ∈ I)
  (he : ∀ j, e j - D (0, v j) = ∑ k, c j k • e k)
  (z₀ : M) (b : κ → R) (h₀ : D (1, z₀) = ∑ j, b j • e j)
include hc he h₀

/-- Finite reduction data construct every full approximate pair with one fixed finite module. -/
theorem exists_kernel_approximations :
    ∃ E : Submodule R N, E.FG ∧ ∀ n : ℕ, ∃ z : M, D (1, z) ∈ I ^ n • E := by
  have hseed : D (1, 0) - (D.comp (LinearMap.inr R R M)) (-z₀) = ∑ j, b j • e j := by
    rw [← one_smul R (D (1, 0)), ← pair_difference, neg_neg]
    exact h₀
  obtain ⟨E, hE, h⟩ := exists_approximations_of_matrix
    (D.comp (LinearMap.inr R R M)) I e v c hc he (D (1, 0)) (-z₀) b hseed
  refine ⟨E, hE, fun n ↦ ?_⟩
  obtain ⟨z, hz⟩ := h n
  refine ⟨-z, ?_⟩
  simpa only [pair_difference, one_smul] using hz

/-- Finite reductions construct an exact kernel pair with multiplier congruent to one. -/
theorem exists_kernel_pair :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ D (a, z) = 0 := by
  have hseed : D (1, 0) - (D.comp (LinearMap.inr R R M)) (-z₀) = ∑ j, b j • e j := by
    rw [← one_smul R (D (1, 0)), ← pair_difference, neg_neg]
    exact h₀
  obtain ⟨a, z, ha, hz⟩ := exists_lift_of_matrix
    (D.comp (LinearMap.inr R R M)) I e v c hc he (D (1, 0)) (-z₀) b hseed
  exact ⟨a, -z, ha, by rw [pair_difference, hz, sub_self]⟩

end FLT.Mazur.FiniteErrorReduction
