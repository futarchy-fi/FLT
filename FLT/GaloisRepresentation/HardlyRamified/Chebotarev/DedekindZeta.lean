/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AINTLIB.CebotarevDensity.NumberFieldEulerProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic asymptotics of Dedekind zeta

The positive residue at one implies that `log (ζ_K(s).re) / log (1 / (s - 1))`
tends to one as the real variable `s` tends to one from above. This is leaf Z1
of `docs/CHEBOTAREV_PLAN.md`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Chebotarev

/-- The logarithmic normalization for prime-ideal sums near one. -/
noncomputable def ell (s : ℝ) : ℝ := Real.log (1 / (s - 1))

/-- The logarithmic normalization tends to positive infinity from the right of one. -/
theorem tendsto_ell_nhdsGT_one : Tendsto ell (𝓝[>] (1 : ℝ)) atTop := by
  have hsub : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (show Tendsto (fun s : ℝ ↦ s) (𝓝[>] 1) (𝓝 1) from
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub_const (1 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr hs
  change Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) _ _
  simpa only [one_div, Function.comp_def] using
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hsub)

/-- The logarithm of Dedekind zeta has leading term `log (1 / (s - 1))` as `s → 1+`. -/
theorem log_dedekindZeta_asymptotic (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ Real.log (NumberField.dedekindZeta K (s : ℂ)).re / ell s)
      (𝓝[>] 1) (𝓝 1) := by
  have hres : Tendsto (fun s : ℝ ↦ (s - 1) * (NumberField.dedekindZeta K s).re)
      (𝓝[>] 1) (𝓝 (NumberField.dedekindZeta_residue K)) := by
    simpa [Function.comp_def, Complex.mul_re] using Complex.continuous_re.tendsto _ |>.comp
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  have hlog := hres.log (NumberField.dedekindZeta_residue_ne_zero K)
  have hlim := (hlog.div_atTop tendsto_ell_nhdsGT_one).const_add 1
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    tendsto_ell_nhdsGT_one.eventually (eventually_gt_atTop 0)] with s hs hell
  have hs0 : s - 1 ≠ 0 := (sub_pos.mpr hs).ne'
  have hz0 : (NumberField.dedekindZeta K (s : ℂ)).re ≠ 0 :=
    (dedekindZeta_re_pos_of_one_lt K s hs).ne'
  rw [Real.log_mul hs0 hz0, add_div]
  have hell_eq : ell s = -Real.log (s - 1) := by
    simp [ell, Real.log_inv]
  have hcancel : Real.log (s - 1) / ell s = -1 := by
    rw [← neg_eq_iff_eq_neg.mpr hell_eq, neg_div, div_self hell.ne']
  rw [hcancel]
  ring

end Chebotarev
