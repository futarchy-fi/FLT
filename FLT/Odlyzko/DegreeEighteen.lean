/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.CertifiedL1

/-!
# The certified degree-eighteen comparison

This is the numerical endpoint of Poitou's equation (26).  The deliberately coarse Euler
lower bound `1/2` already leaves more than `1/25` of logarithmic margin.
-/

@[expose] public section

namespace Odlyzko.Poitou

open _root_.Odlyzko.Interval

/-- The fixed-scale right side of equation (26) at degree `18`. -/
noncomputable def degreeEighteenLowerBound : ℝ :=
  Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
    12 * Real.pi / (5 * 18 * Real.sqrt y0) - L1large y0

private theorem degree_eighteen_margin_aux :
    Real.log 8.25 + 1 / 25 ≤ degreeEighteenLowerBound := by
  have hgamma := Constants.eulerGamma_mem_coarse.1
  have hpi := Constants.pi_mem .digits6
  have hlogLower :=
    (Constants.log_mem (392699 / 31250) 80 (by norm_num)).1
  have hlogTarget := (Constants.log_mem (33 / 4) 80 (by norm_num)).2
  have hL := L1_y0_mem.2
  have harg : (392699 / 31250 : ℝ) ≤ 4 * Real.pi := by
    norm_num [Constants.piEnclosure] at hpi
    nlinarith
  have hlog4pi : Real.log (392699 / 31250 : ℝ) ≤ Real.log (Real.pi * 4) := by
    simpa [mul_comm] using Real.log_le_log (by norm_num) harg
  norm_num [Constants.eulerGammaCoarseEnclosure,
    _root_.Odlyzko.Interval.RatIvl.sub, Constants.logEnclosure,
    Constants.logArgument, Constants.logOneMinusEnclosure,
    Constants.logOneMinusSum, Constants.logOneMinusError] at hgamma hlogLower hlogTarget
  norm_num [Constants.piEnclosure] at hpi
  rw [degreeEighteenLowerBound, sqrt_y0]
  norm_num [L1Enclosure] at hL ⊢
  ring_nf at ⊢
  nlinarith [hgamma, hpi.2, hlogLower, hlogTarget, hlog4pi, hL]

/-- The degree-eighteen lower bound exceeds `log 8.25`. -/
theorem degree_eighteen_bound : Real.log 8.25 ≤ degreeEighteenLowerBound := by
  linarith [degree_eighteen_margin_aux]

/-- An explicit positive margin retained by the coarse rational certificate. -/
theorem degree_eighteen_margin :
    1 / 25 ≤ degreeEighteenLowerBound - Real.log 8.25 := by
  linarith [degree_eighteen_margin_aux]

end Odlyzko.Poitou
