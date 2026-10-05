/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.NumberField.UnramifiedPrimeSupport

/-!
# Global discriminant bounds from finitely many local bounds

If the different exponent above each exceptional prime `q` is at most
`c q` times its ramification index, the discriminant divides
`(∏ q ∈ S, q ^ c q) ^ [K : ℚ]`. The local bounds are explicit hypotheses.
-/

@[expose] public noncomputable section

open UniqueFactorizationMonoid

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Primewise normalized different bounds clear to a single ideal containment. -/
theorem span_prod_le_different_of_exponent_bounds (S : Finset ℕ) (c : ℕ → ℕ)
    (hprime : ∀ q ∈ S, q.Prime)
    (hbound : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], ∀ q ∈ S, (q : 𝓞 K) ∈ P →
      differentExponentAt K P ≤ c q * P.ramificationIdx ℤ)
    (hu : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (∀ q ∈ S, (q : 𝓞 K) ∉ P) →
      Algebra.IsUnramifiedAt ℤ P) :
    Ideal.span {((∏ q ∈ S, q ^ c q : ℕ) : 𝓞 K)} ≤ differentIdeal ℤ (𝓞 K) := by
  classical
  have hne (q : ℕ) (hq : q ∈ S) : Ideal.span {(q : 𝓞 K)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using
      (hprime q hq).ne_zero
  have hprod : (∏ q ∈ S, Ideal.span {(q : 𝓞 K)} ^ c q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q hq ↦ pow_ne_zero _ (hne q hq))
  have heq : Ideal.span {((∏ q ∈ S, q ^ c q : ℕ) : 𝓞 K)} =
      ∏ q ∈ S, Ideal.span {(q : 𝓞 K)} ^ c q := by
    simp only [Nat.cast_prod, Nat.cast_pow, Ideal.span_singleton_pow, Ideal.prod_span_singleton]
  rw [heq, ← Ideal.dvd_iff_le,
    dvd_iff_normalizedFactors_le_normalizedFactors differentIdeal_ne_bot hprod]
  apply Multiset.le_iff_count.mpr
  intro P
  change differentExponentAt K P ≤ _
  by_cases hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K))
  · have hp := (Ideal.mem_normalizedFactors_iff differentIdeal_ne_bot).mp hmem
    have : P.IsPrime := hp.1
    by_cases hex : ∃ q ∈ S, (q : 𝓞 K) ∈ P
    · obtain ⟨q, hq, hqP⟩ := hex
      have : P.LiesOver (Ideal.span {(q : ℤ)}) :=
        (Ideal.liesOver_span_iff hp.1.ne_top
          (Nat.prime_iff_prime_int.mp (hprime q hq))).mpr
            (by simpa only [map_natCast] using hqP)
      have hdvd : Ideal.span {(q : 𝓞 K)} ^ c q ∣
          ∏ r ∈ S, Ideal.span {(r : 𝓞 K)} ^ c r := Finset.dvd_prod_of_mem _ hq
      have hc := Multiset.count_le_of_le P
        ((dvd_iff_normalizedFactors_le_normalizedFactors
          (pow_ne_zero _ (hne q hq)) hprod).mp hdvd)
      rw [normalizedFactors_pow, Multiset.count_nsmul,
        count_normalizedFactors_span_prime_eq_ramificationIdx K P q (hprime q hq)] at hc
      exact (hbound P q hq hqP).trans hc
    · push Not at hex
      rw [differentExponentAt_eq_zero_of_isUnramifiedAt K P (hu P hex)]
      exact Nat.zero_le _
  · rw [show differentExponentAt K P = 0 from Multiset.count_eq_zero.mpr hmem]
    exact Nat.zero_le _

/-- Local different bounds bound the absolute discriminant integrally. -/
theorem natAbs_discr_le_of_exponent_bounds (S : Finset ℕ) (c : ℕ → ℕ)
    (hprime : ∀ q ∈ S, q.Prime)
    (hbound : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], ∀ q ∈ S, (q : 𝓞 K) ∈ P →
      differentExponentAt K P ≤ c q * P.ramificationIdx ℤ)
    (hu : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (∀ q ∈ S, (q : 𝓞 K) ∉ P) →
      Algebra.IsUnramifiedAt ℤ P) :
    (discr K).natAbs ≤ (∏ q ∈ S, q ^ c q) ^ Module.finrank ℚ K := by
  have hpos : 0 < ∏ q ∈ S, q ^ c q :=
    Finset.prod_pos (fun q hq ↦ pow_pos (hprime q hq).pos _)
  simpa only [pow_one] using natAbs_discr_pow_le_of_span_le_different_pow K
    (∏ q ∈ S, q ^ c q) 1 hpos
    (by simpa only [pow_one] using
      span_prod_le_different_of_exponent_bounds K S c hprime hbound hu)

end NumberField
