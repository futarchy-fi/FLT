/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteErrorLinearLifting
public import Mathlib.LinearAlgebra.Prod

/-!
# Exact multiplier and correction pairs from finite errors

Approximate pairs have scalar coordinate one. A single finite module controls
their full equation errors at every ideal power. The resulting exact pair has
scalar congruent to one, hence nonvanishing at any prime containing the ideal.
No compatibility between the successive approximate pairs is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorLinearLifting
variable {R M N : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (D : (R × M) →ₗ[R] N) (I : Ideal R) (E : Submodule R N) (hE : E.FG)

include hE in
/-- All-order approximate kernel pairs produce an exact pair with scalar congruent to one. -/
theorem exists_kernel_pair
    (h : ∀ n : ℕ, ∃ z : M, D (1, z) ∈ I ^ n • E) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ D (a, z) = 0 := by
  let F := D.comp (LinearMap.inr R R M)
  have he : ∀ n : ℕ, ∃ z : M, D (1, 0) - F z ∈ I ^ n • E := by
    intro n
    obtain ⟨z, hz⟩ := h n
    refine ⟨-z, ?_⟩
    have hd : D (1, 0) - F (-z) = D (1, z) := by
      change D (1, 0) - D (0, -z) = D (1, z)
      rw [← map_sub]
      congr 1
      ext <;> simp
    rwa [hd]
  obtain ⟨a, z, ha, hz⟩ := exists_scaled_lift_of_errors F I E hE (D (1, 0)) he
  refine ⟨a, -z, ha, ?_⟩
  calc
    D (a, -z) = D (a • (1, 0) - (0, z)) := by
      congr 1
      ext <;> simp
    _ = a • D (1, 0) - F z := by rw [map_sub, map_smul]; rfl
    _ = 0 := by rw [hz, sub_self]

include hE in
/-- The exact kernel pair is nonvanishing on the closed locus of the approximation ideal. -/
theorem exists_kernel_pair_nonvanishing
    (h : ∀ n : ℕ, ∃ z : M, D (1, z) ∈ I ^ n • E)
    (P : Ideal R) (hIP : I ≤ P) (hP : P ≠ ⊤) :
    ∃ (a : R) (z : M), a ∉ P ∧ D (a, z) = 0 := by
  obtain ⟨a, z, ha, hz⟩ := exists_kernel_pair D I E hE h
  exact ⟨a, z, multiplier_not_mem I P hIP hP ha, hz⟩

/-- It suffices to control errors modulo exact corrections in a finite cokernel submodule. -/
theorem exists_kernel_pair_of_cokernel
    (Q : Submodule R (N ⧸ LinearMap.range (D.comp (LinearMap.inr R R M))))
    (hQ : Q.FG)
    (h : ∀ n : ℕ, (LinearMap.range (D.comp (LinearMap.inr R R M))).mkQ
      (D (1, 0)) ∈ I ^ n • Q) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ D (a, z) = 0 := by
  obtain ⟨a, z, ha, hz⟩ :=
    exists_scaled_lift (D.comp (LinearMap.inr R R M)) I Q hQ (D (1, 0)) h
  refine ⟨a, -z, ha, ?_⟩
  calc
    D (a, -z) = D (a • (1, 0) - (0, z)) := by
      congr 1
      ext <;> simp
    _ = a • D (1, 0) - D (0, z) := by rw [map_sub, map_smul]
    _ = 0 := by rw [← hz]; exact sub_self _

end FLT.Mazur.FiniteErrorLinearLifting
