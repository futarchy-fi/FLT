/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Discard

/-!
# The scaled Odlyzko inequality

This file names the one-variable lower bound consumed by the numerical endgame.  The caller
supplies the archimedean integral and pole transform for the scaled family `F_y`; scaling itself
is kept separate.  With Poitou's normalization, the pole correction is subtracted once, rather
than multiplied by the field degree.
-/

@[expose] public section

namespace Odlyzko

open Module NumberField

/-- The degree-independent part of the totally-complex root-discriminant lower bound. -/
noncomputable def L1 (archimedeanIntegral : ℝ → ℂ) : ℝ → ℝ :=
  fun y ↦ archimedeanLowerTerm (archimedeanIntegral y)

/-- The two pole values in the explicit formula, collected as one real correction. -/
noncomputable def poleCorrection (phi : ℝ → ℂ → ℂ) : ℝ → ℝ :=
  fun y ↦ (phi y 0 + phi y 1).re

/-- Q5: after specializing to a totally complex field and dividing the discard inequality by
the positive degree, all degree dependence is the single term `poleCorrection phi y / n`. -/
theorem L1_sub_poleCorrection_div_finrank_le_log_discriminant_div_finrank
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (F : ℝ → ℝ → ℂ) (phi : ℝ → ℂ → ℂ)
    (zeroSide archimedeanIntegral primeSide : ℝ → ℂ)
    (y : ℝ) (_hy : 0 < y) (hdegree : 1 ≤ finrank ℚ K)
    (hformula : TotallyComplexExplicitFormula K (F y) (phi y) (zeroSide y)
      (archimedeanIntegral y) (primeSide y))
    (hF0 : F y 0 = 1) (hzero : 0 ≤ (zeroSide y).re)
    (hprime : 0 ≤ (primeSide y).re) :
    L1 archimedeanIntegral y - poleCorrection phi y / finrank ℚ K ≤
      Real.log |(discr K : ℝ)| / finrank ℚ K := by
  have hn : (0 : ℝ) < finrank ℚ K := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdegree)
  apply (le_div_iff₀ hn).2
  have hdiscard := discriminant_log_ge_archimedean_sub_poles K (F y) (phi y)
    (zeroSide y) (archimedeanIntegral y) (primeSide y) hformula hF0 hzero hprime
  rw [sub_mul, div_mul_cancel₀ _ hn.ne']
  simpa [L1, poleCorrection, mul_comm] using hdiscard

end Odlyzko
