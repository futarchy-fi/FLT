/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDiscrepancySeparation

/-!
# One annihilator for the entire adically vanishing submodule

Artin--Rees and the determinant form of Nakayama produce one scalar congruent
to one that kills every element of the intersection of all ideal powers.
The scalar is uniform even for an infinite family of discrepancies. Its ring
is the ring over which the ambient module is finite.
-/

@[expose] public section
namespace FLT.Mazur.AdicDiscrepancySeparation
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsNoetherianRing R] [Module.Finite R M]

/-- A single scalar annihilates the entire intersection of the adic filtration. -/
theorem exists_uniform_annihilator (I : Ideal R) :
    ∃ s : R, 1 - s ∈ I ∧
      ∀ x : M, (∀ n : ℕ, x ∈ (I ^ (n + 1) • ⊤ : Submodule R M)) → s • x = 0 := by
  let N : Submodule R M := ⨅ n : ℕ, I ^ n • ⊤
  have hN : ∀ k, (I.stableFiltration ⊤ ⊓ I.trivialFiltration N).N k = N :=
    fun k ↦ inf_eq_right.mpr ((iInf_le _ k).trans (le_of_eq (by simp)))
  have hIN : N ≤ I • N := by
    obtain ⟨k, hk⟩ := (I.stableFiltration_stable ⊤).inter_right (I.trivialFiltration N)
    have h := hk k (le_refl _)
    rw [hN, hN] at h
    exact le_of_eq h.symm
  obtain ⟨r, hr, hx⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    I N (IsNoetherian.noetherian N) hIN
  refine ⟨1 - r, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using hr
  · intro x h
    have hxN : x ∈ N := by
      rw [Submodule.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n => exact h n
    rw [sub_smul, one_smul, hx x hxN, sub_self]

/-- A ring scalar kills every adically vanishing element simultaneously. -/
theorem exists_uniform_ring_annihilator (I : Ideal R) :
    ∃ s : R, 1 - s ∈ I ∧
      ∀ x : R, (∀ n : ℕ, x ∈ I ^ (n + 1)) → s * x = 0 := by
  obtain ⟨s, hs, h⟩ := exists_uniform_annihilator (M := R) I
  refine ⟨s, hs, fun x hx ↦ h x ?_⟩
  intro n
  simpa only [smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hx n

/-- The same uniform annihilator avoids every proper ideal containing the adic ideal. -/
theorem exists_uniform_annihilator_outside (I P : Ideal R) (hIP : I ≤ P) (hP : P ≠ ⊤) :
    ∃ s : R, s ∉ P ∧ 1 - s ∈ I ∧
      ∀ x : M, (∀ n : ℕ, x ∈ (I ^ (n + 1) • ⊤ : Submodule R M)) → s • x = 0 := by
  obtain ⟨s, hs, hx⟩ := exists_uniform_annihilator (M := M) I
  refine ⟨s, ?_, hs, hx⟩
  intro h
  exact hP (P.eq_top_iff_one.mpr (by simpa using P.add_mem (hIP hs) h))

end FLT.Mazur.AdicDiscrepancySeparation
