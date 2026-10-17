/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCokernelReductionFrame
public import FLT.Mazur.FiniteReductionKernelPairs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Full kernel pairs from finite cokernel data

The finite frame and every correction are constructed in the entire target.
Over a local ring the multiplier is a unit, so the constructed pair can be
normalized to scalar one. No completion or Noetherian hypothesis is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (D : (R × M) →ₗ[R] N) (I : Ideal R)
set_option quotPrecheck false
local notation "F" => D.comp (LinearMap.inr R R M)
local notation "π" => (LinearMap.range F).mkQ
variable (Q : Submodule R (N ⧸ LinearMap.range (D.comp (LinearMap.inr R R M))))

/-- Finite cokernel data construct the actual finite full-equation kernel reduction. -/
theorem exists_kernel_reduction_of_cokernel (hQ : Q.FG) (hred : Q ≤ I • Q)
    (hseed : π (D (1, 0)) ∈ Q) :
    ∃ (n : ℕ) (e : Fin n → N) (v : Fin n → M) (c : Fin n → Fin n → R)
      (z₀ : M) (b : Fin n → R),
      (∀ j k, c j k ∈ I) ∧
      (∀ j, e j - D (0, v j) = ∑ k, c j k • e k) ∧
      D (1, z₀) = ∑ j, b j • e j := by
  obtain ⟨n, e, v, c, z, b, hc, hv, hb⟩ :=
    exists_full_reduction F I Q hQ hred (D (1, 0)) hseed
  refine ⟨n, e, v, c, -z, b, hc, hv, ?_⟩
  simpa only [pair_difference, one_smul] using hb

/-- Cokernel finiteness and one-step divisibility produce an exact full kernel pair. -/
theorem exists_kernel_pair_of_cokernel (hQ : Q.FG) (hred : Q ≤ I • Q)
    (hseed : π (D (1, 0)) ∈ Q) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ D (a, z) = 0 := by
  obtain ⟨n, e, v, c, z, b, hc, hv, hb⟩ :=
    exists_kernel_reduction_of_cokernel D I Q hQ hred hseed
  exact exists_kernel_pair D I e v c hc hv z b hb

/-- The same constructed finite frame controls every full approximation order. -/
theorem exists_kernel_approximations_of_cokernel (hQ : Q.FG) (hred : Q ≤ I • Q)
    (hseed : π (D (1, 0)) ∈ Q) :
    ∃ E : Submodule R N, E.FG ∧ ∀ n : ℕ, ∃ z : M, D (1, z) ∈ I ^ n • E := by
  obtain ⟨n, e, v, c, z, b, hc, hv, hb⟩ :=
    exists_kernel_reduction_of_cokernel D I Q hQ hred hseed
  exact exists_kernel_approximations D I e v c hc hv z b hb

/-- A unit multiplier in a full kernel pair can be normalized without dropping equations. -/
theorem normalize_kernel_pair {a : R} (ha : IsUnit a) {z : M} (hz : D (a, z) = 0) :
    ∃ w : M, D (1, w) = 0 := by
  obtain ⟨a, rfl⟩ := ha
  refine ⟨(↑a⁻¹ : R) • z, ?_⟩
  have he : (1, (↑a⁻¹ : R) • z) = (↑a⁻¹ : R) • ((a : R), z) := by
    ext <;> simp
  rw [he, map_smul, hz, smul_zero]

/-- Local finite cokernel divisibility constructs an exact pair with scalar exactly one. -/
theorem exists_local_kernel_pair [IsLocalRing R] (hQ : Q.FG)
    (hred : Q ≤ IsLocalRing.maximalIdeal R • Q) (hseed : π (D (1, 0)) ∈ Q) :
    ∃ z : M, D (1, z) = 0 := by
  obtain ⟨a, z, ha, hz⟩ :=
    exists_kernel_pair_of_cokernel D (IsLocalRing.maximalIdeal R) Q hQ hred hseed
  apply normalize_kernel_pair D (z := z) _ hz
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hm
  have h1 := (IsLocalRing.maximalIdeal R).sub_mem hm ha
  rw [sub_sub_cancel] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end FLT.Mazur.FiniteErrorReduction
