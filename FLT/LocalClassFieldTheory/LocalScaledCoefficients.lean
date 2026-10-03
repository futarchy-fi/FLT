/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalLogConvergence
public import FLT.LocalClassFieldTheory.LocalScaledSeries

/-!
# Integral coefficients of scaled exp and log

The coefficients of (exp(pX)-1)/p and log(1+pX)/p lie in the DVR.
The improved factorial estimate includes the division by p.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open PowerSeries IsLocalRing IsDedekindDomain

variable {L : Type*} [Field L] [CharZero L]

/-- Positive coefficients of the scaled exponential. -/
theorem localScaledExp_coeff_succ (a : L) (ha : a ≠ 0) (n : ℕ) :
    coeff (n + 1) (localScaledSeries a (exp L - 1)) =
      a ^ n / ((n + 1).factorial : L) := by
  simp [localScaledSeries, coeff_rescale, coeff_exp, coeff_one,
    pow_succ, smul_eq_mul, mul_assoc, ha, mul_left_comm, div_eq_mul_inv]

/-- Positive coefficients of the scaled logarithm. -/
theorem localScaledLog_coeff_succ (a : L) (ha : a ≠ 0) (n : ℕ) :
    coeff (n + 1) (localScaledSeries a (log L)) =
      (-1 : L) ^ n * a ^ n / ((n + 1 : ℕ) : L) := by
  simp [localScaledSeries, coeff_rescale, coeff_log,
    pow_succ, smul_eq_mul, mul_assoc, ha, mul_left_comm, div_eq_mul_inv]

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [CharZero L] in
/-- The factorial valuation bound after removing the initial linear factor. -/
theorem dvr_valuation_factorial_succ_lower (n : ℕ) :
    ((dvrPrime S).valuation L (p : L)) ^ n ≤
      (dvrPrime S).valuation L ((n + 1).factorial : L) := by
  rw [dvr_valuation_factorial S L p]
  apply pow_le_pow_right_of_le_one'
  · rw [← map_natCast (algebraMap S L)]
    exact HeightOneSpectrum.valuation_le_one (dvrPrime S) (p : S)
  · exact Nat.le_of_lt_succ (padicValNat_factorial_lt_of_ne_zero p (by omega))

/-- Every scaled exponential coefficient is integral for the actual DVR valuation. -/
theorem localScaledExp_coeff_integral (n : ℕ) :
    (dvrPrime S).valuation L (coeff n (localScaledSeries (p : L) (exp L - 1))) ≤ 1 := by
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff, localScaledSeries_constantCoeff _ (by simp)]
    simp
  | succ n =>
    rw [localScaledExp_coeff_succ _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
      map_div₀, map_pow]
    apply (div_le_one₀ (pos_iff_ne_zero.mpr
      ((map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))))).mpr
    exact dvr_valuation_factorial_succ_lower S L p n

/-- Every scaled logarithm coefficient is integral for the actual DVR valuation. -/
theorem localScaledLog_coeff_integral (n : ℕ) :
    (dvrPrime S).valuation L (coeff n (localScaledSeries (p : L) (log L))) ≤ 1 := by
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff, localScaledSeries_constantCoeff _ constantCoeff_log]
    simp
  | succ n =>
    rw [localScaledLog_coeff_succ _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
    simp only [map_div₀, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    apply (div_le_one₀ (pos_iff_ne_zero.mpr
      ((map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))))).mpr
    exact dvr_valuation_succ_lower S L p n

end LocalClassFieldTheory
