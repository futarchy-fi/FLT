/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.LogEulerProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Bounded logarithmic Euler remainder

This proves part (ii) and the conclusion of leaf Z3 in `docs/CHEBOTAREV_PLAN.md`.
The explicit bound holds for every real `s > 1`, strengthening the planned
interval `1 < s < 3/2`. As in Z2 and Z3(i), the plan's `Prime K` and `norm`
are spelled out using `HeightOneSpectrum` and `Ideal.absNorm`; `ps` is
`NumberField.Set.primeIdealZetaSum`.
-/

public section

open NumberField IsDedekindDomain Filter
open scoped Topology

namespace Chebotarev

/-- A uniform quadratic bound for the logarithmic Euler remainder on `[0, 1/2]`. -/
theorem abs_neg_log_one_sub_sub_le {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |x| < 1 by rw [abs_of_nonneg hx]; linarith) 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one,
    abs_of_nonneg hx] at h
  have hb : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - x)).2
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]
  calc
    |-Real.log (1 - x) - x| = |x + Real.log (1 - x)| := by
      rw [show -Real.log (1 - x) - x = -(x + Real.log (1 - x)) by ring, abs_neg]
    _ ≤ 2 * x ^ 2 := h.trans hb

/-- The logarithmic prime-ideal Euler series differs from its linear term by
at most twice the convergent prime-ideal norm series at exponent two. -/
theorem logEuler_remainder_le (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    |(∑' v : HeightOneSpectrum (𝓞 K),
        -Real.log (1 - (v.asIdeal.absNorm : ℝ) ^ (-s))) -
      ∑' v : HeightOneSpectrum (𝓞 K), (v.asIdeal.absNorm : ℝ) ^ (-s)| ≤
      2 * ∑' v : HeightOneSpectrum (𝓞 K), (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) := by
  have hbound (v : HeightOneSpectrum (𝓞 K)) :
      |-Real.log (1 - (v.asIdeal.absNorm : ℝ) ^ (-s)) -
        (v.asIdeal.absNorm : ℝ) ^ (-s)| ≤
        2 * (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) := by
    have hn0 : v.asIdeal.absNorm ≠ 0 := fun h ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    have hn1 : v.asIdeal.absNorm ≠ 1 := fun h ↦
      v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have hn : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast (show 2 ≤ v.asIdeal.absNorm by omega)
    have hnonneg : 0 ≤ (v.asIdeal.absNorm : ℝ) := by positivity
    have hx : (v.asIdeal.absNorm : ℝ) ^ (-s) ≤ 1 / 2 := by
      calc
        _ ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ 1 / 2 := by
          rw [Real.rpow_neg_one]
          simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hn)
    apply (abs_neg_log_one_sub_sub_le (Real.rpow_nonneg hnonneg _) hx).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← Real.rpow_mul_natCast hnonneg]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num
    linarith
  rw [← (summable_neg_log_one_sub_primeNorm K s hs).tsum_sub
    (summable_primeNorm K s hs)]
  have hmajor := (summable_primeNorm K 2 (by norm_num)).mul_left 2
  calc
    _ ≤ ∑' v : HeightOneSpectrum (𝓞 K), 2 * (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) := by
      rw [← Real.norm_eq_abs]
      apply tsum_of_norm_bounded hmajor.hasSum
      intro v
      simpa only [Real.norm_eq_abs] using hbound v
    _ = _ := tsum_mul_left

/-- The logarithm of Dedekind zeta differs from the sum over all prime ideals
by a bounded function as the real parameter tends to one from above. -/
theorem log_zeta_sub_primeSum_bounded (K : Type*) [Field K] [NumberField K] :
    Asymptotics.IsBigO (𝓝[>] (1 : ℝ))
      (fun s ↦ Real.log (NumberField.dedekindZeta K (s : ℂ)).re -
        NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s)
      (fun _ ↦ (1 : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * ∑' v : HeightOneSpectrum (𝓞 K),
    (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < s := hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one,
    log_dedekindZeta_eq_tsum_primeIdeal K s hs']
  rw [NumberField.Set.primeIdealZetaSum_def,
    tsum_univ (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.asIdeal.absNorm : ℝ) ^ (-s))]
  exact logEuler_remainder_le K s hs'

end Chebotarev
