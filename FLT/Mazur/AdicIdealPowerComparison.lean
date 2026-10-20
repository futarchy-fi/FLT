/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Comparing rank ideal powers with original scalar powers

If the entire scalar fiber is supported on a rank locus, finite generation
of its defining ideal gives a uniform cofinality bound. The result controls
the full ideal powers, not merely the reduced support used to obtain the bound.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicIdealPowerComparison
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (J : Ideal R) (K : Ideal B)

/-- Finite generation turns radical containment into one positive bound for all powers. -/
theorem exists_power_bound (hK : K.FG) (h : K ≤ (J.map (algebraMap R B)).radical) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, K ^ (c * n) ≤ (J ^ n).map (algebraMap R B) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h hK
  have hs : K ^ (c + 1) ≤ J.map (algebraMap R B) :=
    (Ideal.pow_le_pow_right (Nat.le_succ c)).trans hc
  refine ⟨c + 1, Nat.zero_lt_succ c, fun n ↦ ?_⟩
  rw [pow_mul, Ideal.map_pow]
  exact pow_le_pow_left' hs n

/-- Full scalar-fiber support gives the same uniform bound on nonreduced ideal powers. -/
theorem exists_power_bound_of_support (hK : K.FG)
    (h : PrimeSpectrum.zeroLocus (J.map (algebraMap R B) : Set B) ⊆
      PrimeSpectrum.zeroLocus (K : Set B)) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, K ^ (c * n) ≤ (J ^ n).map (algebraMap R B) :=
  exists_power_bound J K hK (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _ |>.mp h)

/-- Ambient rank errors at a cofinal order are errors in the original scalar module. -/
theorem mem_scalar_power_of_mem_rank_power {c n : ℕ}
    (h : K ^ (c * n) ≤ (J ^ n).map (algebraMap R B)) {x : B}
    (hx : x ∈ K ^ (c * n)) : x ∈ J ^ n • (⊤ : Submodule R B) := by
  rw [Ideal.smul_top_eq_map]
  exact h hx

/-- A cofinal subsequence of rank approximations yields every original scalar approximation. -/
theorem scalar_approximations {A : Type*} (F : A → B) (x : B)
    (hK : K.FG) (h : K ≤ (J.map (algebraMap R B)).radical)
    (hv : ∀ k : ℕ, ∃ v : A, x - F v ∈ K ^ (k + 1)) :
    ∀ n : ℕ, ∃ v : A, x - F v ∈ J ^ (n + 1) • (⊤ : Submodule R B) := by
  obtain ⟨c, hc, hbound⟩ := exists_power_bound J K hK h
  intro n
  obtain ⟨v, hv⟩ := hv (c * (n + 1) - 1)
  have hpos : 0 < c * (n + 1) := Nat.mul_pos hc (Nat.zero_lt_succ n)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))] at hv
  exact ⟨v, mem_scalar_power_of_mem_rank_power J K (hbound (n + 1)) hv⟩

end FLT.Mazur.AdicIdealPowerComparison
