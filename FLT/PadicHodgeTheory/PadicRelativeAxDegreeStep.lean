/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AxDegreeBudget
public import FLT.PadicHodgeTheory.PadicBinomialDescent
public import FLT.PadicHodgeTheory.PadicRelativeHasseApproximation
public import FLT.PadicHodgeTheory.PadicAxDegreeStep

/-! # Strict relative algebraic degree reduction with a bounded arithmetic budget -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- Every nonscalar algebraic point has an actual lower-degree approximant.
Both the new displacement bound and its accumulated loss are proved, not postulated. -/
theorem padicRelativeAx_degree_step (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : Gal(PadicAlgCl p/E), ‖σ a - a‖ ≤ r)
    (hn : 1 < (minpoly E a).natDegree) :
    ∃ (b : PadicAlgCl p) (d : ℝ),
      (minpoly E b).natDegree < (minpoly E a).natDegree ∧ 1 ≤ d ∧
      ‖a - b‖ ≤ d * r ∧ (∀ σ : Gal(PadicAlgCl p/E), ‖σ b - b‖ ≤ d * r) ∧
      axDegreeFactor p (minpoly E b).natDegree * d ≤
        axDegreeFactor p (minpoly E a).natDegree := by
  obtain ⟨k, d, hk, hkn, hd, hdpow, hbudget⟩ := padicAx_exists_degree_budget p hn
  obtain ⟨b, hbdeg, hb⟩ := padicRelativeHasse_exists_approximation p E a hr ha hk hkn.le
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hbr : ‖a - b‖ ≤ d * r := by
    apply le_of_pow_le_pow_left₀ hk.ne' (mul_nonneg hd0 hr)
    simpa only [mul_pow, hdpow, div_eq_mul_inv, mul_comm] using hb
  have hrdr : r ≤ d * r := by simpa using mul_le_mul_of_nonneg_right hd hr
  refine ⟨b, d, hbdeg.trans_lt hkn, hd, hbr, ?_, ?_⟩
  · simpa only [max_eq_right hrdr] using padicRelativeGalois_displacement_nearby p E a b ha hbr
  · exact (mul_le_mul_of_nonneg_right
      (axDegreeFactor_mono hp.out.one_lt.le
        (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral b)) hbdeg) hd0).trans hbudget

end PadicHodgeTheory
