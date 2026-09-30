/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Omega

/-!
# Effectivity of coefficients with self-pairing one

The final coefficient calculation in Snowden, Proposition 9.2.1: an integral
coefficient vector of square norm one has a single coefficient equal to ±1.
Positive constituent dimensions and total dimension two force the positive sign.
-/

@[expose] public section

namespace GaloisRepresentation

/-- Self-pairing one and dimension two force a single effective constituent
of dimension two. -/
theorem effective_of_square_sum_one {ι : Type*} [Fintype ι]
    (n : ι → ℤ) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hself : ∑ i, (n i) ^ 2 = 1) (hdim : ∑ i, n i * (d i : ℤ) = 2) :
    ∃ i, d i = 2 ∧ n i = 1 ∧ ∀ j, j ≠ i → n j = 0 := by
  classical
  have hpos : 0 < ∑ i, (n i) ^ 2 := by omega
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j _ ↦ sq_nonneg (n j))).mp hpos
  have hbound : (n i) ^ 2 ≤ 1 := by
    simpa only [hself] using Finset.single_le_sum
      (fun j _ ↦ sq_nonneg (n j)) (Finset.mem_univ i)
  have hiunit : (n i) ^ 2 = 1 := by omega
  have herase : ∑ j ∈ Finset.univ.erase i, (n j) ^ 2 = 0 := by
    have hs := Finset.sum_erase_add Finset.univ (fun j ↦ (n j) ^ 2) (Finset.mem_univ i)
    rw [hself, hiunit] at hs
    omega
  have hzero : ∀ j, j ≠ i → n j = 0 := by
    intro j hji
    have hj : (n j) ^ 2 ≤ ∑ k ∈ Finset.univ.erase i, (n k) ^ 2 :=
      Finset.single_le_sum (fun k _ ↦ sq_nonneg (n k))
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    rw [herase] at hj
    nlinarith [sq_nonneg (n j)]
  have hdim' : n i * (d i : ℤ) = 2 := by
    rw [Finset.sum_eq_single i] at hdim
    · exact hdim
    · intro j _ hji
      rw [hzero j hji, zero_mul]
    · simp
  have hdi : 0 < (d i : ℤ) := by exact_mod_cast hd i
  have hni : n i = 1 := by
    have hsign : n i = 1 ∨ n i = -1 := by
      have : n i < 0 ∨ 0 ≤ n i := lt_or_ge (n i) 0
      rcases this with hn | hn
      · right
        nlinarith
      · left
        nlinarith
    rcases hsign with hn | hn
    · exact hn
    · rw [hn] at hdim'
      nlinarith
  refine ⟨i, ?_, hni, hzero⟩
  rw [hni, one_mul] at hdim'
  exact_mod_cast hdim'

end GaloisRepresentation
