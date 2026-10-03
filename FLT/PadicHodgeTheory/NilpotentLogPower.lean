/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.NilpotentSeriesSubstitution
public import FLT.PadicHodgeTheory.PowerSeriesLogPower
public import Mathlib.Algebra.Ring.GeomSum

/-! # The finite logarithm identity for powers of unipotent elements -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- A finite logarithm polynomial, with the standard rational coefficients. -/
def finiteNilpotentLog (r : ℕ) (x : R) : R :=
  ∑ i ∈ Finset.range r, coeff i (log R) * x ^ i

omit [Algebra ℚ R] in
/-- Taking an integer power preserves the same nilpotence bound for the difference from one. -/
theorem unipotent_pow_sub_one_nilpotent_bound {x : R} {r : ℕ} (hx : x ^ r = 0) (n : ℕ) :
    ((1 + x) ^ n - 1) ^ r = 0 := by
  have hd : x ∣ (1 + x) ^ n - 1 := by
    simpa only [add_sub_cancel_left] using sub_one_dvd_pow_sub_one (1 + x) n
  obtain ⟨a, ha⟩ := hd
  rw [ha, mul_pow, hx, zero_mul]

/-- Nilpotent evaluation realizes every sufficiently long logarithm truncation. -/
theorem finiteNilpotentLog_eq_eval {x : R} {r : ℕ} (hx : x ^ r = 0) :
    finiteNilpotentLog r x = nilpotentSeriesEval ⟨r, hx⟩ (log R) :=
  (nilpotentSeriesEval_eq_sum ⟨r, hx⟩ r hx (log R)).symm

/-- The exact finite logarithm/power identity; the truncation bound is unchanged. -/
theorem finiteNilpotentLog_pow {x : R} {r : ℕ} (hx : x ^ r = 0) (n : ℕ) :
    finiteNilpotentLog r ((1 + x) ^ n - 1) = n • finiteNilpotentLog r x := by
  let e := nilpotentSeriesEval (show IsNilpotent x from ⟨r, hx⟩)
  have hg : constantCoeff ((1 + X : PowerSeries R) ^ n - 1) = 0 := by simp
  have h := congrArg e (powerSeriesLogOf_pow (R := R) (f := 1 + X) (by simp) n)
  rw [logOf_eq, nilpotentSeriesEval_subst ⟨r, hx⟩ hg, map_nsmul,
    logOf_one_add_X] at h
  have hv : e ((1 + X : PowerSeries R) ^ n - 1) = (1 + x) ^ n - 1 := by
    simp [e]
  have hy : (e ((1 + X : PowerSeries R) ^ n - 1)) ^ r = 0 := by
    rw [hv]
    exact unipotent_pow_sub_one_nilpotent_bound hx n
  rw [nilpotentSeriesEval_eq_sum _ r hy] at h
  change (∑ i ∈ Finset.range r, coeff i (log R) *
    e ((1 + X : PowerSeries R) ^ n - 1) ^ i) = n • e (log R) at h
  rw [hv] at h
  simpa only [finiteNilpotentLog, e, nilpotentSeriesEval_eq_sum _ r hx] using h

end PadicHodgeTheory
