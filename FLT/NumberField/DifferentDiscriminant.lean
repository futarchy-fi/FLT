/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discriminant bounds from containment in powers of the different

Clearing the denominators of local different-exponent bounds gives an
inclusion of integral ideals. Taking norms turns that inclusion into a
divisibility statement for the absolute discriminant. In particular, the
Fontaine constants `2/3` and `3/2` have common denominator six.

This file proves only the global comparison; it does not assert the local
Fontaine bound or the required containment in the different.
-/

@[expose] public noncomputable section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- An integer in a power of the different gives divisibility by the
corresponding power of the absolute discriminant. -/
theorem natAbs_discr_pow_dvd_of_span_le_different_pow (a m : ℕ)
    (h : Ideal.span {(a : 𝓞 K)} ≤ differentIdeal ℤ (𝓞 K) ^ m) :
    (discr K).natAbs ^ m ∣ a ^ Module.finrank ℚ K := by
  have hn := Ideal.absNorm_dvd_absNorm_of_le h
  simpa only [map_pow, absNorm_differentIdeal K (𝓞 K),
    Ideal.absNorm_span_natCast, RingOfIntegers.rank] using hn

/-- A positive integer in a power of the different bounds the corresponding
power of the absolute discriminant. -/
theorem natAbs_discr_pow_le_of_span_le_different_pow (a m : ℕ) (ha : 0 < a)
    (h : Ideal.span {(a : 𝓞 K)} ≤ differentIdeal ℤ (𝓞 K) ^ m) :
    (discr K).natAbs ^ m ≤ a ^ Module.finrank ℚ K :=
  Nat.le_of_dvd (pow_pos ha _) (natAbs_discr_pow_dvd_of_span_le_different_pow K a m h)

/-- The ideal containment obtained by clearing the local exponents `2/3`
and `3/2` implies the desired real discriminant inequality. -/
theorem discr_le_fontaine_of_span_le_different_pow
    (h : Ideal.span {((2 : 𝓞 K) ^ 4 * 3 ^ 9)} ≤ differentIdeal ℤ (𝓞 K) ^ 6) :
    |(discr K : ℝ)| ≤
      ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ)) ^ Module.finrank ℚ K := by
  have hn := natAbs_discr_pow_le_of_span_le_different_pow K (2 ^ 4 * 3 ^ 9) 6
    (by norm_num) (by simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h)
  have hr : |(discr K : ℝ)| ^ 6 ≤
      ((2 : ℝ) ^ 4 * 3 ^ 9) ^ Module.finrank ℚ K := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hn
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_natAbs, Int.cast_abs] using hc
  have h2 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 6 = (2 : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h3 : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ 6 = (3 : ℝ) ^ 9 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  apply le_of_pow_le_pow_left₀ (n := 6) (by norm_num) (by positivity)
  rwa [← pow_mul, Nat.mul_comm (Module.finrank ℚ K) 6, pow_mul, mul_pow, h2, h3]

end NumberField
