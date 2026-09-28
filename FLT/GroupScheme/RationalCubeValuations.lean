/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.NormNum

/-!
# Rational cubes and prime valuations

A rational number is a cube exactly when every prime valuation is divisible
by three. The sign causes no obstruction for an odd power.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- Divisibility of all prime factorization exponents by three constructs a
cube root of a natural number. -/
theorem nat_cube_of_factorization (a : ℕ)
    (h : ∀ p : ℕ, p.Prime → 3 ∣ a.factorization p) :
    ∃ b : ℕ, b ^ 3 = a := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  refine ⟨a.factorization.prod fun p k ↦ p ^ (k / 3), ?_⟩
  rw [← powMonoidHom_apply, map_finsuppProd]
  nth_rw 2 [← Nat.prod_factorization_pow_eq_self ha]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  rw [powMonoidHom_apply, ← pow_mul,
    Nat.div_mul_cancel (h p (Nat.prime_of_mem_primeFactors hp))]

/-- An integer whose prime factorization exponents are divisible by three
is a cube, with the sign incorporated in its root. -/
theorem int_cube_of_factorization (a : ℤ)
    (h : ∀ p : ℕ, p.Prime → 3 ∣ a.natAbs.factorization p) :
    ∃ b : ℤ, b ^ 3 = a := by
  obtain ⟨b, hb⟩ := nat_cube_of_factorization a.natAbs h
  rcases Int.natAbs_eq a with ha | ha
  · refine ⟨b, ?_⟩
    rw [ha]
    exact_mod_cast hb
  · refine ⟨-(b : ℤ), ?_⟩
    have hb' : (b : ℤ) ^ 3 = (a.natAbs : ℤ) := by exact_mod_cast hb
    rw [neg_pow, hb', ha]
    norm_num

/-- Divisibility of a rational valuation passes separately to numerator and
denominator, since they are coprime. -/
theorem num_den_dvd_padicVal {a : ℚ} {p d : ℕ} (hp : p.Prime)
    (h : (d : ℤ) ∣ padicValRat p a) :
    d ∣ padicValInt p a.num ∧ d ∣ padicValNat p a.den := by
  rcases Rat.num_or_den_zero_padicVal a hp with hn | hd
  · simp only [padicValRat_def, hn, Nat.cast_zero, zero_sub, dvd_neg,
      Int.natCast_dvd_natCast] at h
    exact ⟨by simp [hn], h⟩
  · simp only [padicValRat_def, hd, Nat.cast_zero, sub_zero,
      Int.natCast_dvd_natCast] at h
    exact ⟨h, by simp [hd]⟩

/-- A rational number is a cube if and only if every prime valuation is a
multiple of three. -/
theorem rational_cube_iff_valuations (a : ℚ) :
    (∃ b : ℚ, b ^ 3 = a) ↔ ∀ p : ℕ, p.Prime → (3 : ℤ) ∣ padicValRat p a := by
  constructor
  · rintro ⟨b, rfl⟩ p hp
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.pow]
    exact dvd_mul_right _ _
  · intro h
    obtain ⟨n, hn⟩ := int_cube_of_factorization a.num fun p hp ↦ by
      have := (num_den_dvd_padicVal hp (h p hp)).1
      simpa only [Nat.factorization_def _ hp, padicValInt] using this
    obtain ⟨d, hd⟩ := nat_cube_of_factorization a.den fun p hp ↦ by
      have := (num_den_dvd_padicVal hp (h p hp)).2
      rwa [Nat.factorization_def _ hp]
    refine ⟨(n : ℚ) / d, ?_⟩
    rw [div_pow, ← Int.cast_pow, ← Nat.cast_pow, hn, hd]
    exact Rat.num_div_den a

end ThreeAdicPlan
