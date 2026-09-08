/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.ExplicitFormula

/-!
# The Odlyzko discard inequality

Taking real parts of the totally-complex explicit formula, normalizing `F 0 = 1`, and dropping
the nonnegative zero and prime sides gives the logarithmic discriminant inequality.  The factor
`finrank ℚ K` multiplies the entire archimedean constant-minus-integral term; the pole term is
subtracted exactly once.
-/

@[expose] public section

namespace Odlyzko

open Module NumberField

/-- The archimedean constant-minus-integral term appearing in the discard inequality. -/
noncomputable def archimedeanLowerTerm (archimedeanIntegral : ℂ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) - archimedeanIntegral.re

/-- P5: discard the nonnegative zero and prime sides and rearrange the explicit formula. -/
theorem discriminant_log_ge_archimedean_sub_poles
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (F : ℝ → ℂ) (phi : ℂ → ℂ)
    (zeroSide archimedeanIntegral primeSide : ℂ)
    (hformula : TotallyComplexExplicitFormula K F phi zeroSide archimedeanIntegral primeSide)
    (hF0 : F 0 = 1) (hzero : 0 ≤ zeroSide.re) (hprime : 0 ≤ primeSide.re) :
    (finrank ℚ K : ℝ) * archimedeanLowerTerm archimedeanIntegral -
        (phi 0 + phi 1).re ≤ Real.log |(discr K : ℝ)| := by
  have h := congrArg Complex.re hformula.formula
  rw [hF0] at h
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero, mul_one] at h
  unfold archimedeanLowerTerm
  rw [Complex.add_re]
  linarith

end Odlyzko
