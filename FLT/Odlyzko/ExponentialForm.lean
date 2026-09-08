/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Exponential form of a logarithmic root-discriminant bound

This is endgame node S3.  It converts the logarithmic bound produced by S2 to the natural
power used by `Odlyzko_statement`; no real-power operation appears in the conclusion.
-/

@[expose] public section

namespace Odlyzko

open Module NumberField

/-- Exponentiating a normalized logarithmic lower bound gives a natural-power bound. -/
theorem pow_le_of_log_div_le {x : ℝ} {n : ℕ}
    (hx : 0 < x) (hn : 0 < n)
    (hlog : Real.log 8.25 ≤ Real.log x / n) :
    (8.25 : ℝ) ^ n ≤ x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : (n : ℝ) * Real.log 8.25 ≤ Real.log x := by
    simpa [mul_comm] using (le_div_iff₀ hnR).mp hlog
  calc
    (8.25 : ℝ) ^ n = Real.exp (Real.log 8.25) ^ n := by
      rw [Real.exp_log]
      norm_num
    _ = Real.exp ((n : ℝ) * Real.log 8.25) := (Real.exp_nat_mul _ n).symm
    _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hmul
    _ = x := Real.exp_log hx

/-- Field-facing S3: the conclusion has the natural-power shape used by
`Odlyzko_statement`.  Total complexity and the degree cutoff belong to S2;
here they have already been consumed to produce `hlog`. -/
theorem discriminant_ge_pow_of_log_bound
    (K : Type*) [Field K] [NumberField K]
    (hlog : Real.log 8.25 ≤
      Real.log |(discr K : ℝ)| / finrank ℚ K) :
    |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K := by
  apply pow_le_of_log_div_le
  · exact abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  · exact Module.finrank_pos_iff.mpr inferInstance
  · exact hlog

end Odlyzko
