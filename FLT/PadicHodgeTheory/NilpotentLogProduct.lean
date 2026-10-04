/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.NilpotentLogPower

/-! # Finite logarithms multiply to sums in a principal nilpotent ideal -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Evaluating a formal logarithm gives the finite logarithm of the evaluated difference. -/
theorem nilpotentSeriesEval_logOf {t : R} (ht : IsNilpotent t)
    {f : PowerSeries R} (hf : constantCoeff f = 1) (r : ℕ)
    (hr : (nilpotentSeriesEval ht f - 1) ^ r = 0) :
    nilpotentSeriesEval ht (logOf f) = finiteNilpotentLog r (nilpotentSeriesEval ht f - 1) := by
  have hsub : constantCoeff (f - 1) = 0 := by simp [hf]
  rw [logOf_eq, nilpotentSeriesEval_subst ht hsub]
  have he : nilpotentSeriesEval ht (f - 1) = nilpotentSeriesEval ht f - 1 := by simp
  rw [nilpotentSeriesEval_eq_sum _ r (by simpa only [he] using hr)]
  simp only [he, finiteNilpotentLog]

/-- Products of elements congruent to one modulo a principal nilpotent ideal add logarithms. -/
theorem finiteNilpotentLog_mul {t : R} {r : ℕ} (ht : t ^ r = 0) (a b : R) :
    finiteNilpotentLog r ((1 + t * a) * (1 + t * b) - 1) =
      finiteNilpotentLog r (t * a) + finiteNilpotentLog r (t * b) := by
  let e := nilpotentSeriesEval (show IsNilpotent t from ⟨r, ht⟩)
  let f : PowerSeries R := 1 + C a * X
  let g : PowerSeries R := 1 + C b * X
  have hf : constantCoeff f = 1 := by simp [f]
  have hg : constantCoeff g = 1 := by simp [g]
  have hef : e f = 1 + t * a := by simp [e, f, mul_comm]
  have heg : e g = 1 + t * b := by simp [e, g, mul_comm]
  dsimp only [e] at hef heg
  have hprod : ((1 + t * a) * (1 + t * b) - 1) ^ r = 0 := by
    have h : (1 + t * a) * (1 + t * b) - 1 = t * (a + b + t * a * b) := by ring
    rw [h, mul_pow, ht, zero_mul]
  have ha : (t * a) ^ r = 0 := by rw [mul_pow, ht, zero_mul]
  have hb : (t * b) ^ r = 0 := by rw [mul_pow, ht, zero_mul]
  have h := congrArg e (powerSeriesLogOf_mul hf hg)
  rw [map_add, nilpotentSeriesEval_logOf ⟨r, ht⟩ (by simp [hf, hg]) r
      (by simpa only [map_mul, hef, heg] using hprod),
    nilpotentSeriesEval_logOf ⟨r, ht⟩ hf r (by simpa only [hef, add_sub_cancel_left] using ha),
    nilpotentSeriesEval_logOf ⟨r, ht⟩ hg r (by simpa only [heg, add_sub_cancel_left] using hb)] at h
  simpa only [map_mul, hef, heg, add_sub_cancel_left] using h

end PadicHodgeTheory
