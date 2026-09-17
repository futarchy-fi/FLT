/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.AINTLIB.DedekindResidue.CompletedZeta.DualLattice
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# First leaves of the zeta functional-equation tree

This file records nodes A1 and F2a from `cartography/zeta-fe-decomposition.md`.
Node A1 is re-exported from the vendored AINTLIB dual-lattice module. For F2a, we prove the
two archimedean Gamma integrals in Deligne's normalization.
-/

@[expose] public section

open MeasureTheory Set

namespace Complex

/-- The real archimedean Gamma integral in Deligne's normalization. -/
theorem integral_exp_neg_pi_mul_cpow_div_eq_gammaR {c : ℝ} {s : ℂ}
    (hc : 0 < c) (hs : 0 < s.re) :
    (∫ y : ℝ in Ioi 0, exp (-(((Real.pi * c : ℝ) : ℂ) * (y : ℂ))) *
      (y : ℂ) ^ (s / 2) / (y : ℂ)) = Gammaℝ s * (c : ℂ) ^ (-s / 2) := by
  rw [show (∫ y : ℝ in Ioi 0, exp (-(((Real.pi * c : ℝ) : ℂ) * (y : ℂ))) *
      (y : ℂ) ^ (s / 2) / (y : ℂ)) =
      ∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s / 2 - 1) *
        exp (-(((Real.pi * c : ℝ) : ℂ) * (y : ℂ))) by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [cpow_sub _ _ (ofReal_ne_zero.mpr (ne_of_gt hy)), cpow_one]
    ring]
  rw [integral_cpow_mul_exp_neg_mul_Ioi (a := s / 2) (r := Real.pi * c)
    (by simpa using half_pos hs) (mul_pos Real.pi_pos hc), Gammaℝ_def]
  have harg : (((Real.pi * c : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg (mul_nonneg Real.pi_pos.le hc.le)]
    exact Real.pi_ne_zero.symm
  rw [one_div, inv_cpow _ _ harg, ← cpow_neg, ofReal_mul,
    mul_cpow_ofReal_nonneg Real.pi_pos.le hc.le]
  ring_nf

/-- The complex archimedean Gamma integral in Deligne's normalization. -/
theorem integral_exp_neg_two_pi_mul_cpow_div_eq_gammaC {c : ℝ} {s : ℂ}
    (hc : 0 < c) (hs : 0 < s.re) :
    (∫ y : ℝ in Ioi 0, exp (-((((2 * Real.pi) * c : ℝ) : ℂ) * (y : ℂ))) *
      (y : ℂ) ^ s / (y : ℂ)) = (1 / 2 : ℂ) * Gammaℂ s * (c : ℂ) ^ (-s) := by
  rw [show (∫ y : ℝ in Ioi 0, exp (-((((2 * Real.pi) * c : ℝ) : ℂ) * (y : ℂ))) *
      (y : ℂ) ^ s / (y : ℂ)) =
      ∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s - 1) *
        exp (-((((2 * Real.pi) * c : ℝ) : ℂ) * (y : ℂ))) by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [cpow_sub _ _ (ofReal_ne_zero.mpr (ne_of_gt hy)), cpow_one]
    ring]
  rw [integral_cpow_mul_exp_neg_mul_Ioi (a := s) (r := (2 * Real.pi) * c)
    hs (mul_pos (mul_pos (by norm_num) Real.pi_pos) hc), Gammaℂ_def]
  have harg : ((((2 * Real.pi) * c : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hc.le)]
    exact Real.pi_ne_zero.symm
  rw [one_div, inv_cpow _ _ harg, ← cpow_neg, ofReal_mul,
    mul_cpow_ofReal_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hc.le,
    ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
  have htwopi : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-s) =
      (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
    simpa using (mul_cpow_ofReal_nonneg (r := -s)
      (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
  rw [htwopi]
  norm_num
  ring

end Complex
