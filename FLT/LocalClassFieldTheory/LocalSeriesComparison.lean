/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicSeriesField
public import FLT.LocalClassFieldTheory.LocalIntegralSeries
public import FLT.LocalClassFieldTheory.LocalLogUniformConvergence

/-!
# Integral evaluation agrees with the fraction-field analytic series

The scaled integral series evaluate to (exp(pt)-1)/p and log(1+pt)/p.
This connects formal substitution identities to the actual convergent sums.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open PowerSeries IsLocalRing

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- The local exponential in the actual adic fraction-field topology. -/
def adicLocalExp (x : L) : L :=
  letI := dvrAdicValued S L
  ∑' n : ℕ, x ^ n / (n.factorial : L)

/-- Evaluation of the integral exponential recovers the usual exponential sum. -/
theorem adicLocalExp_eq_integral (t : AdicInteger S L)
    (ht : (dvrPrime S).valuation L (adicIntegerToField S L t) < 1) :
    adicLocalExp S L ((p : L) * adicIntegerToField S L t) =
      1 + (p : L) * adicIntegerToField S L
        (adicSeriesEval S L (integralExpSeries S L p) t) := by
  let := dvrAdicValued S L
  have h := (hasSum_nat_add_iff' (f := fun n =>
    algebraMap S L (coeff n (integralExpSeries S L p)) * adicIntegerToField S L t ^ n)
    1).mpr (adicSeriesEval_field_hasSum S L (integralExpSeries S L p) t ht)
  simp only [Finset.sum_range_one, coeff_zero_eq_constantCoeff,
    integralExpSeries_constantCoeff, map_zero, zero_mul, sub_zero] at h
  have hc (n : ℕ) : algebraMap S L (coeff (n + 1) (integralExpSeries S L p)) =
      (p : L) ^ n / ((n + 1).factorial : L) := by
    rw [← coeff_map, integralExpSeries_map,
      localScaledExp_coeff_succ _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  have hs : HasSum (fun n : ℕ =>
      ((p : L) * adicIntegerToField S L t) ^ (n + 1) / ((n + 1).factorial : L))
      ((p : L) * adicIntegerToField S L
        (adicSeriesEval S L (integralExpSeries S L p) t)) := by
    convert h.mul_left (p : L) using 1
    funext n
    rw [hc]
    simp only [mul_pow, pow_succ, div_eq_mul_inv]
    ring
  have hs' := (hasSum_nat_add_iff (f := fun n : ℕ =>
    ((p : L) * adicIntegerToField S L t) ^ n / (n.factorial : L)) 1).mp hs
  simpa only [adicLocalExp, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, add_comm] using hs'.tsum_eq

/-- Evaluation of the integral logarithm recovers the usual logarithm sum. -/
theorem adicLocalLog_eq_integral (t : AdicInteger S L)
    (ht : (dvrPrime S).valuation L (adicIntegerToField S L t) < 1) :
    adicLocalLog S L (1 + (p : L) * adicIntegerToField S L t) =
      (p : L) * adicIntegerToField S L
        (adicSeriesEval S L (integralLogSeries S L p) t) := by
  let := dvrAdicValued S L
  have h := (hasSum_nat_add_iff' (f := fun n =>
    algebraMap S L (coeff n (integralLogSeries S L p)) * adicIntegerToField S L t ^ n)
    1).mpr (adicSeriesEval_field_hasSum S L (integralLogSeries S L p) t ht)
  simp only [Finset.sum_range_one, coeff_zero_eq_constantCoeff,
    integralLogSeries_constantCoeff, map_zero, zero_mul, sub_zero] at h
  have hc (n : ℕ) : algebraMap S L (coeff (n + 1) (integralLogSeries S L p)) =
      (-1 : L) ^ n * (p : L) ^ n / ((n + 1 : ℕ) : L) := by
    rw [← coeff_map, integralLogSeries_map,
      localScaledLog_coeff_succ _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  have hs : HasSum (localLogTerm ((p : L) * adicIntegerToField S L t))
      ((p : L) * adicIntegerToField S L
        (adicSeriesEval S L (integralLogSeries S L p) t)) := by
    convert h.mul_left (p : L) using 1
    funext n
    rw [hc]
    simp only [localLogTerm, mul_pow, pow_succ, div_eq_mul_inv]
    ring
  simpa only [adicLocalLog, add_sub_cancel_left] using hs.tsum_eq

end LocalClassFieldTheory
