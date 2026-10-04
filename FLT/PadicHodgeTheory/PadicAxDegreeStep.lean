/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AxDegreeBudget
public import FLT.PadicHodgeTheory.PadicBinomialDescent
public import FLT.PadicHodgeTheory.PadicHasseApproximation

/-! # Strict algebraic degree reduction with a bounded arithmetic budget -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- Choose an interior Hasse degree whose exact binomial loss fits the budget. -/
theorem padicAx_exists_degree_budget {n : ℕ} (hn : 1 < n) :
    ∃ (k : ℕ) (d : ℝ), 0 < k ∧ k < n ∧ 1 ≤ d ∧
      d ^ k = ‖(n.choose k : ℚ_[p])‖⁻¹ ∧ axDegreeFactor p k * d ≤ axDegreeFactor p n := by
  rcases padicBinomial_degree_cases p hn with ⟨k, hk, hkn, hu⟩ | ⟨s, rfl⟩
  · refine ⟨k, 1, hk, hkn, le_rfl, ?_, ?_⟩
    · simp [hu]
    · simpa using axDegreeFactor_mono hp.out.one_lt.le hk hkn.le
  · have hk : 0 < p ^ s := pow_pos hp.out.pos _
    have hkn : 2 * p ^ s ≤ p ^ (s + 1) := by
      rw [pow_succ']
      exact Nat.mul_le_mul_right _ hp.out.two_le
    refine ⟨p ^ s, (p : ℝ) ^ (1 / ((p ^ s : ℕ) : ℝ)), hk, by omega, ?_, ?_, ?_⟩
    · exact Real.one_le_rpow (by exact_mod_cast hp.out.one_lt.le) (by positivity)
    · rw [axRootFactor_pow hp.out.pos hk, padicBinomial_primePower_norm, inv_inv]
    · exact axDegreeFactor_step hp.out.one_lt.le hk hkn

/-- Every nonscalar algebraic point has an actual lower-degree approximant.
Both the new displacement bound and its accumulated loss are proved, not postulated. -/
theorem padicAx_degree_step (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r)
    (hn : 1 < (minpoly ℚ_[p] a).natDegree) :
    ∃ (b : PadicAlgCl p) (d : ℝ),
      (minpoly ℚ_[p] b).natDegree < (minpoly ℚ_[p] a).natDegree ∧ 1 ≤ d ∧
      ‖a - b‖ ≤ d * r ∧ (∀ σ : PadicGalois p, ‖σ b - b‖ ≤ d * r) ∧
      axDegreeFactor p (minpoly ℚ_[p] b).natDegree * d ≤
        axDegreeFactor p (minpoly ℚ_[p] a).natDegree := by
  obtain ⟨k, d, hk, hkn, hd, hdpow, hbudget⟩ := padicAx_exists_degree_budget p hn
  obtain ⟨b, hbdeg, hb⟩ := padicHasse_exists_approximation p a hr ha hk hkn.le
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hbr : ‖a - b‖ ≤ d * r := by
    apply le_of_pow_le_pow_left₀ hk.ne' (mul_nonneg hd0 hr)
    simpa only [mul_pow, hdpow, div_eq_mul_inv, mul_comm] using hb
  have hrdr : r ≤ d * r := by simpa using mul_le_mul_of_nonneg_right hd hr
  refine ⟨b, d, hbdeg.trans_lt hkn, hd, hbr, ?_, ?_⟩
  · simpa only [max_eq_right hrdr] using padicGalois_displacement_nearby p a b ha hbr
  · exact (mul_le_mul_of_nonneg_right
      (axDegreeFactor_mono hp.out.one_lt.le
        (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral b)) hbdeg) hd0).trans hbudget

end PadicHodgeTheory
