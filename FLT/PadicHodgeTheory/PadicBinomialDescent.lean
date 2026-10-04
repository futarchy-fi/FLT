/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Choose.Factorization

/-! # Binomial choices for arithmetic degree descent -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- A degree greater than one is either a positive p-power or has an interior unit binomial. -/
theorem padicBinomial_degree_cases {n : ℕ} (hn : 1 < n) :
    (∃ k, 0 < k ∧ k < n ∧ ‖(n.choose k : ℚ_[p])‖ = 1) ∨
      ∃ s : ℕ, n = p ^ (s + 1) := by
  by_cases h : ∃ k, 0 < k ∧ k < n ∧ ¬ p ∣ n.choose k
  · left
    obtain ⟨k, hk, hkn, hunit⟩ := h
    exact ⟨k, hk, hkn, Padic.norm_natCast_eq_one_iff.mpr
      (hp.out.coprime_iff_not_dvd.mpr hunit)⟩
  · right
    have he : n = p ^ multiplicity p n := by
      apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat (by omega)
      intro k hk
      apply Nat.modEq_zero_iff_dvd.mpr
      by_contra hnot
      exact h ⟨k, by simp only [Finset.mem_Icc] at hk; omega,
        by simp only [Finset.mem_Icc] at hk; omega, hnot⟩
    have hm : multiplicity p n ≠ 0 := by
      intro hm
      simp only [hm, pow_zero] at he
      omega
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact ⟨s, by simpa only [hs, Nat.succ_eq_add_one] using he⟩

/-- The binomial coefficient for dropping one p-power has p-adic valuation exactly one. -/
theorem padicBinomial_primePower_valuation (s : ℕ) :
    padicValNat p ((p ^ (s + 1)).choose (p ^ s)) = 1 := by
  rw [← Nat.factorization_def _ hp.out, Nat.factorization_choose_prime_pow hp.out
    (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ s)) (pow_ne_zero _ hp.out.ne_zero),
    Nat.factorization_pow_self hp.out]
  omega

/-- The only nonunit loss in the chosen descent step is exactly p. -/
theorem padicBinomial_primePower_norm (s : ℕ) :
    ‖((p ^ (s + 1)).choose (p ^ s) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  have hk : p ^ s ≤ p ^ (s + 1) := Nat.pow_le_pow_right hp.out.pos (Nat.le_succ s)
  rw [Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk)),
    Padic.valuation_natCast, padicBinomial_primePower_valuation, Nat.cast_one,
    zpow_neg_one]

end PadicHodgeTheory
