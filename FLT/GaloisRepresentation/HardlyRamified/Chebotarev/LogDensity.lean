/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.DedekindZeta
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.LogEulerRemainder
import all Mathlib.NumberTheory.NumberField.DirichletDensity -- unfold `HasDirichletDensity`

/-!
# Logarithmic density of prime ideals

The sum over all prime ideals divided by `ell` tends to one. Consequently,
normalizing by `ell` agrees with Mathlib's `HasDirichletDensity`, which instead
divides by the sum over all prime ideals. This proves leaf Z4 of
`docs/CHEBOTAREV_PLAN.md`; the plan's `Prime K` and `ps` are spelled out as
`HeightOneSpectrum (𝓞 K)` and `NumberField.Set.primeIdealZetaSum`.
-/

public section

open NumberField IsDedekindDomain Filter
open scoped Topology

namespace Chebotarev

variable {K : Type*} [Field K] [NumberField K]

/-- A set of prime ideals has logarithmic density `d` if its prime sum divided
by `log (1 / (s - 1))` tends to `d` as `s → 1+`. -/
@[expose] def LogDensity (T : Set (HeightOneSpectrum (𝓞 K))) (d : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ NumberField.Set.primeIdealZetaSum T s / ell s)
    (𝓝[>] 1) (𝓝 d)

/-- The set of all prime ideals has logarithmic density one. -/
theorem logDensity_univ : LogDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  have hsmall := (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
    tendsto_ell_nhdsGT_one
  have herror := ((log_zeta_sub_primeSum_bounded K).trans_isLittleO hsmall).tendsto_div_nhds_zero
  have h := (log_dedekindZeta_asymptotic K).sub herror
  simpa only [LogDensity, Function.comp_def, id_eq, sub_zero, sub_div,
    sub_sub_cancel] using h

/-- Logarithmic normalization and Mathlib's all-prime-sum normalization give
the same Dirichlet density. -/
theorem logDensity_iff_hasDirichletDensity
    (T : Set (HeightOneSpectrum (𝓞 K))) (d : ℝ) :
    LogDensity T d ↔ NumberField.Set.HasDirichletDensity T d := by
  rw [LogDensity, NumberField.Set.HasDirichletDensity]
  have huniv := logDensity_univ (K := K)
  change Tendsto _ _ _ at huniv
  constructor
  · intro h
    have hquot := h.div huniv (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at hquot
    apply hquot.congr'
    filter_upwards [tendsto_ell_nhdsGT_one.eventually (eventually_gt_atTop 0)] with s hs
    exact div_div_div_cancel_right₀ hs.ne' _ _
  · intro h
    have hprod := h.mul huniv
    simp only [mul_one] at hprod
    apply hprod.congr'
    filter_upwards [huniv.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with s hs
    exact div_mul_div_cancel₀ (div_ne_zero_iff.mp hs).1

end Chebotarev
