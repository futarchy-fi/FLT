/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.NumberField.DifferentDiscriminant
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# From primewise different exponents to a discriminant bound

The global different exponent is the multiplicity of a prime in the different
ideal. Bounds `3 d ≤ 2 e` at two and `2 d ≤ 3 e` at three, together with
unramifiedness elsewhere, imply that `(2^4 3^9)` is contained in the sixth
power of the different. No completion comparison or tame different formula
is assumed implicitly.
-/

@[expose] public noncomputable section

open UniqueFactorizationMonoid

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The exponent of a prime ideal in the absolute different. The definition
also makes sense for any ideal; nonprime ideals have exponent zero. -/
def differentExponentAt (P : Ideal (𝓞 K)) : ℕ :=
  (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P

/-- The global primewise different exponent normalized by the ramification
index. Identifying this with the different of a completion is a separate
local-global theorem. -/
def normalizedDifferentExponentAt (P : Ideal (𝓞 K)) : ℚ :=
  (differentExponentAt K P : ℚ) / P.ramificationIdx ℤ

/-- The normalized strict Fontaine inequality gives the integer exponent
inequality used when taking norms. -/
theorem two_mul_differentExponentAt_le_of_normalized_lt
    (P : Ideal (𝓞 K)) [P.IsPrime]
    (h : normalizedDifferentExponentAt K P < (3 / 2 : ℚ)) :
    2 * differentExponentAt K P ≤ 3 * P.ramificationIdx ℤ := by
  have he : (0 : ℚ) < P.ramificationIdx ℤ := by
    exact_mod_cast P.ramificationIdx_pos ℤ
  rw [normalizedDifferentExponentAt, div_lt_iff₀ he] at h
  have hh : (2 : ℚ) * differentExponentAt K P ≤ 3 * P.ramificationIdx ℤ := by
    linarith
  exact_mod_cast hh

/-- Once the tame different formula `d = e - 1` is known, an index dividing
three gives the dyadic exponent bound. This does not prove that formula. -/
theorem three_mul_differentExponentAt_le_of_eq_ramificationIdx_sub_one
    (P : Ideal (𝓞 K)) (he : P.ramificationIdx ℤ ∣ 3)
    (hd : differentExponentAt K P = P.ramificationIdx ℤ - 1) :
    3 * differentExponentAt K P ≤ 2 * P.ramificationIdx ℤ := by
  have hle := Nat.le_of_dvd (by decide : 0 < 3) he
  omega

/-- Unramified primes have zero different exponent. -/
theorem differentExponentAt_eq_zero_of_isUnramifiedAt
    (P : Ideal (𝓞 K)) [P.IsPrime] (h : Algebra.IsUnramifiedAt ℤ P) :
    differentExponentAt K P = 0 := by
  classical
  apply Multiset.count_eq_zero.mpr
  intro hmem
  have hle := (Ideal.mem_normalizedFactors_iff differentIdeal_ne_bot).mp hmem
  exact (not_dvd_differentIdeal_iff.mpr h) (Ideal.dvd_iff_le.mpr hle.2)

/-- At a prime above `p`, the exponent of `(p)` is the ramification index. -/
theorem count_normalizedFactors_span_prime_eq_ramificationIdx
    (P : Ideal (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count P = P.ramificationIdx ℤ := by
  have hn : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast,
      ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hp.ne_zero
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
    (Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (Ideal.span {(p : ℤ)}) P hn).symm

/-- Clearing the denominators in the primewise bounds produces a single
inclusion of integral ideals. -/
theorem span_two_four_mul_three_nine_le_different_pow
    (h2 : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (2 : 𝓞 K) ∈ P →
      3 * differentExponentAt K P ≤ 2 * P.ramificationIdx ℤ)
    (h3 : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (3 : 𝓞 K) ∈ P →
      2 * differentExponentAt K P ≤ 3 * P.ramificationIdx ℤ)
    (hu : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (2 : 𝓞 K) ∉ P → (3 : 𝓞 K) ∉ P →
      Algebra.IsUnramifiedAt ℤ P) :
    Ideal.span {((2 : 𝓞 K) ^ 4 * 3 ^ 9)} ≤ differentIdeal ℤ (𝓞 K) ^ 6 := by
  classical
  have h2ne : Ideal.span {(2 : 𝓞 K)} ≠ ⊥ := by simp
  have h3ne : Ideal.span {(3 : 𝓞 K)} ≠ ⊥ := by simp
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    ← Ideal.span_singleton_pow, ← Ideal.dvd_iff_le,
    dvd_iff_normalizedFactors_le_normalizedFactors
      (pow_ne_zero 6 differentIdeal_ne_bot)
      (mul_ne_zero (pow_ne_zero 4 h2ne) (pow_ne_zero 9 h3ne)),
    normalizedFactors_mul (pow_ne_zero 4 h2ne) (pow_ne_zero 9 h3ne)]
  apply Multiset.le_iff_count.mpr
  intro P
  simp only [normalizedFactors_pow, Multiset.count_nsmul, Multiset.count_add]
  change 6 * differentExponentAt K P ≤ _
  by_cases hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K))
  · have hP := (Ideal.mem_normalizedFactors_iff differentIdeal_ne_bot).mp hmem
    have : P.IsPrime := hP.1
    by_cases htwo : (2 : 𝓞 K) ∈ P
    · have : P.LiesOver (Ideal.span {(2 : ℤ)}) :=
        (Ideal.liesOver_span_iff hP.1.ne_top
          (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 2))).mpr
          (by simpa only [map_natCast, Nat.cast_ofNat, map_ofNat] using htwo)
      have hb := h2 P htwo
      have hc := count_normalizedFactors_span_prime_eq_ramificationIdx K P 2 (by decide)
      norm_num only [Nat.cast_ofNat] at hc
      rw [hc]
      omega
    · by_cases hthree : (3 : 𝓞 K) ∈ P
      · have : P.LiesOver (Ideal.span {(3 : ℤ)}) :=
          (Ideal.liesOver_span_iff hP.1.ne_top
            (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 3))).mpr
            (by simpa only [map_natCast, Nat.cast_ofNat, map_ofNat] using hthree)
        have hb := h3 P hthree
        have hc := count_normalizedFactors_span_prime_eq_ramificationIdx K P 3 (by decide)
        norm_num only [Nat.cast_ofNat] at hc
        rw [hc]
        omega
      · rw [differentExponentAt_eq_zero_of_isUnramifiedAt K P (hu P htwo hthree), mul_zero]
        exact Nat.zero_le _
  · have hz : differentExponentAt K P = 0 := Multiset.count_eq_zero.mpr hmem
    rw [hz, mul_zero]
    exact Nat.zero_le _

/-- Primewise different bounds and unramifiedness away from two and three
suffice for the global Fontaine discriminant inequality. -/
theorem discr_le_fontaine_of_differentExponent_bounds
    (h2 : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (2 : 𝓞 K) ∈ P →
      3 * differentExponentAt K P ≤ 2 * P.ramificationIdx ℤ)
    (h3 : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (3 : 𝓞 K) ∈ P →
      2 * differentExponentAt K P ≤ 3 * P.ramificationIdx ℤ)
    (hu : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (2 : 𝓞 K) ∉ P → (3 : 𝓞 K) ∉ P →
      Algebra.IsUnramifiedAt ℤ P) :
    |(discr K : ℝ)| ≤
      ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ)) ^ Module.finrank ℚ K :=
  discr_le_fontaine_of_span_le_different_pow K
    (span_two_four_mul_three_nine_le_different_pow K h2 h3 hu)

end NumberField
