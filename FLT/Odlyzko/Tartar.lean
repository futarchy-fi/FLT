/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.AdmissibleAutocorrelation
public import FLT.Odlyzko.PoitouKernel

/-!
# Tartar's auxiliary function and the instantiation of the autocorrelation package

Poitou (1977), §7.2, records Tartar's construction of the test function used in the
unconditional discriminant bound.  It starts from the concrete profile

`v t = max (1 - t ^ 2) 0`,

sets `w = v ⋆ v` and takes for numerator `f = ĝ ^ 2` where `g = 𝓕 v`; so `f̂` is proportional
to `w`.  This file supplies `v` under the name `tartarV` together with the four structural
properties (nonnegativity, evenness, continuity, compact support in `[-1, 1]`) and the
Lipschitz constant `2`, and then *instantiates* the abstract theorems already proved in
`FLT.Odlyzko.Autocorrelation`, `FLT.Odlyzko.AutocorrelationNonnegative` and
`FLT.Odlyzko.PoitouKernel` at `tartarV`.  Nothing abstract is re-proved here.

The two headline specializations are

* `realAutocorrelation_tartarV_nonneg` : `w = v ⋆ v ≥ 0` pointwise, and
* `fourier_autocorrelation_tartarV_nonneg` : `𝓕 w = ‖𝓕 v‖ ^ 2 ≥ 0` pointwise.

Together they are `autocorrelation_tartarV_and_fourier_nonneg`, which is exactly the pair of
positivity hypotheses consumed downstream by the Poitou kernel.

## Closed form

`realAutocorrelation_tartarV_eq` computes `w` explicitly on `0 ≤ u ≤ 2` as
`-(1/30) (u ^ 5 - 20 u ^ 3 + 40 u ^ 2 - 32)`, matching Poitou §7.2; in particular
`realAutocorrelation_tartarV_zero : w 0 = 16 / 15`.

## Admissibility

The derivative side conditions of `autocorrelation_isAdmissibleTestFn` (existence of a
derivative for the exponentially weighted autocorrelation and for the difference quotient,
together with the integrability of those derivatives on `Set.Ici 0`) are *not* discharged
here: they are genuine one-dimensional analytic estimates and are out of scope for this
packet.  `autocorrelation_tartarV_isAdmissibleTestFn` therefore keeps them as explicit
hypothesis arguments and only discharges the structural inputs (`Function.Even`,
`Continuous`, `HasCompactSupport`, `LipschitzWith 2`) from the facts proved below.
-/

@[expose] public section

open scoped FourierTransform
open MeasureTheory

namespace Odlyzko

/-! ### The function -/

/-- Tartar's auxiliary function `v t = max (1 - t ^ 2) 0`, the concrete input to the
Odlyzko/Poitou autocorrelation construction (Poitou 1977, §7.2). -/
def tartarV : ℝ → ℝ := fun t ↦ max (1 - t ^ 2) 0

@[simp] theorem tartarV_apply (t : ℝ) : tartarV t = max (1 - t ^ 2) 0 := rfl

/-- `tartarV` is pointwise nonnegative. -/
theorem tartarV_nonneg (t : ℝ) : 0 ≤ tartarV t := le_max_right _ _

/-- `tartarV` is an even function. -/
theorem tartarV_even : Function.Even tartarV := by
  intro t
  simp [tartarV]

/-- `tartarV` is continuous. -/
theorem continuous_tartarV : Continuous tartarV :=
  (continuous_const.sub (continuous_pow 2)).max continuous_const

/-- `tartarV` vanishes outside `[-1, 1]`. -/
theorem tartarV_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : tartarV t = 0 := by
  have h : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  simp only [tartarV_apply, max_eq_right_iff]
  linarith

/-- The support of `tartarV` is contained in `[-1, 1]`. -/
theorem support_tartarV_subset : Function.support tartarV ⊆ Set.Icc (-1) 1 := by
  intro t ht
  simp only [Function.mem_support, tartarV_apply, ne_eq, max_eq_right_iff, not_le] at ht
  rw [Set.mem_Icc]
  constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]

/-- `tartarV` has compact support (contained in `[-1, 1]`). -/
theorem hasCompactSupport_tartarV : HasCompactSupport tartarV :=
  HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc fun _t ht ↦
    Function.notMem_support.mp fun h ↦ ht (support_tartarV_subset h)

/-- `tartarV` is integrable. -/
theorem integrable_tartarV : Integrable tartarV :=
  continuous_tartarV.integrable_of_hasCompactSupport hasCompactSupport_tartarV

/-- `tartarV` is square integrable. -/
theorem memLp_tartarV : MemLp tartarV 2 volume :=
  continuous_tartarV.memLp_of_hasCompactSupport hasCompactSupport_tartarV

/-- The clamped description of `tartarV`, used for the Lipschitz estimate. -/
theorem tartarV_eq_one_sub_min_sq (t : ℝ) : tartarV t = 1 - min |t| 1 ^ 2 := by
  rcases le_total |t| 1 with h | h
  · have h2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [min_eq_left h, sq_abs, tartarV_apply, max_eq_left (by linarith)]
  · have h2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [min_eq_right h, tartarV_apply, max_eq_right (by linarith)]
    norm_num

/-- `tartarV` is Lipschitz with constant `2`. -/
theorem lipschitzWith_tartarV : LipschitzWith 2 tartarV := by
  have key : ∀ x y : ℝ, dist (tartarV x) (tartarV y) ≤ (2 : ℝ) * dist x y := by
    intro x y
    rw [Real.dist_eq, Real.dist_eq, tartarV_eq_one_sub_min_sq, tartarV_eq_one_sub_min_sq]
    set a := min |x| 1 with ha
    set b := min |y| 1 with hb
    have ha0 : 0 ≤ a := le_min (abs_nonneg x) zero_le_one
    have hb0 : 0 ≤ b := le_min (abs_nonneg y) zero_le_one
    have ha1 : a ≤ 1 := min_le_right _ _
    have hb1 : b ≤ 1 := min_le_right _ _
    have hab : |a - b| ≤ |x - y| := by
      refine (abs_min_sub_min_le_max |x| 1 |y| 1).trans ?_
      simp only [sub_self, abs_zero]
      exact max_le (abs_abs_sub_abs_le_abs_sub x y) (abs_nonneg _)
    have hsum : |(-(a + b))| ≤ 2 := by
      rw [abs_neg, abs_of_nonneg (by linarith)]
      linarith
    have hrw : 1 - a ^ 2 - (1 - b ^ 2) = (a - b) * (-(a + b)) := by ring
    rw [hrw, abs_mul]
    calc |a - b| * |(-(a + b))| ≤ |x - y| * 2 :=
          mul_le_mul hab hsum (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |x - y| := by ring
  exact LipschitzWith.of_dist_le_mul (by simpa using key)

/-! ### Instantiation of the abstract autocorrelation package

Nothing below is a new theorem: each statement is an application of a theorem already proved
abstractly in `FLT.Odlyzko.Autocorrelation`, `FLT.Odlyzko.AutocorrelationNonnegative` or
`FLT.Odlyzko.PoitouKernel`. -/

/-- **Q3′, first half.** Tartar's `w = v ⋆ v` is pointwise nonnegative. -/
theorem realAutocorrelation_tartarV_nonneg (u : ℝ) : 0 ≤ realAutocorrelation tartarV u :=
  realAutocorrelation_nonneg tartarV tartarV_nonneg u

/-- **Q3′, second half.** The Fourier transform of Tartar's `w` is pointwise nonnegative. -/
theorem fourier_autocorrelation_tartarV_nonneg (t : ℝ) :
    0 ≤ (𝓕 (autocorrelation tartarV) t).re :=
  fourier_autocorrelation_nonneg tartarV integrable_tartarV t

/-- The complex autocorrelation of `tartarV` has nonnegative real part. -/
theorem autocorrelation_tartarV_re_nonneg (x : ℝ) : 0 ≤ (autocorrelation tartarV x).re :=
  autocorrelation_re_nonneg_of_nonneg tartarV tartarV_nonneg x

/-- `𝓕 w = ‖𝓕 v‖ ^ 2` for Tartar's function. -/
theorem fourier_autocorrelation_tartarV (t : ℝ) :
    𝓕 (autocorrelation tartarV) t = ‖𝓕 (complexify tartarV) t‖ ^ 2 :=
  fourier_autocorrelation tartarV integrable_tartarV t

/-- The abstract sufficient-condition package of `FLT.Odlyzko.AutocorrelationNonnegative`,
instantiated at Tartar's function: `w ≥ 0` and `ŵ ≥ 0` simultaneously. -/
theorem autocorrelation_tartarV_and_fourier_nonneg :
    (∀ x, 0 ≤ (autocorrelation tartarV x).re) ∧
      ∀ t, 0 ≤ (𝓕 (autocorrelation tartarV) t).re :=
  autocorrelation_and_fourier_nonneg tartarV integrable_tartarV tartarV_nonneg

/-- The Q1 structural package of `FLT.Odlyzko.Autocorrelation`, instantiated at Tartar's
function. -/
theorem autocorrelation_tartarV_structural_package :
    Function.Even (autocorrelation tartarV) ∧
      HasCompactSupport (autocorrelation tartarV) ∧
      Continuous (autocorrelation tartarV) ∧
      ∀ t, 𝓕 (autocorrelation tartarV) t = ‖𝓕 (complexify tartarV) t‖ ^ 2 ∧
        0 ≤ (𝓕 (autocorrelation tartarV) t).re :=
  autocorrelation_structural_package tartarV tartarV_even continuous_tartarV
    hasCompactSupport_tartarV memLp_tartarV

/-- Tartar's `w` is even. -/
theorem autocorrelation_tartarV_even : Function.Even (autocorrelation tartarV) :=
  autocorrelation_even tartarV tartarV_even

/-- Tartar's `w` has compact support. -/
theorem hasCompactSupport_autocorrelation_tartarV :
    HasCompactSupport (autocorrelation tartarV) :=
  autocorrelation_hasCompactSupport tartarV hasCompactSupport_tartarV

/-- Tartar's `w` is continuous. -/
theorem continuous_autocorrelation_tartarV : Continuous (autocorrelation tartarV) :=
  continuous_autocorrelation tartarV continuous_tartarV hasCompactSupport_tartarV

/-- Fourier positivity in the form consumed by the Poitou boundary identification. -/
theorem fourier_realAutocorrelation_tartarV_nonneg (t : ℝ) :
    0 ≤ (𝓕 (complexify (realAutocorrelation tartarV)) t).re :=
  fourier_realAutocorrelation_nonneg tartarV integrable_tartarV t

/-- The Poitou kernel built from Tartar's `w` is even. -/
theorem poitouKernel_realAutocorrelation_tartarV_even :
    Function.Even (poitouKernel (realAutocorrelation tartarV)) :=
  poitouKernel_even fun x ↦ by
    have h := autocorrelation_tartarV_even x
    rw [autocorrelation_eq_ofReal_realAutocorrelation,
      autocorrelation_eq_ofReal_realAutocorrelation] at h
    exact_mod_cast h

/-- The Poitou kernel built from Tartar's `w` has nonnegative real part. -/
theorem poitouKernel_realAutocorrelation_tartarV_re_nonneg (x : ℝ) :
    0 ≤ (poitouKernel (realAutocorrelation tartarV) x).re :=
  poitouKernel_re_nonneg realAutocorrelation_tartarV_nonneg x

/-! ### Closed form of the autocorrelation

Poitou (1977), §7.2: with `w = v ⋆ v` one has, for `0 ≤ u ≤ 2`,
`w u = -(1/30) (u ^ 5 - 20 u ^ 3 + 40 u ^ 2 - 32)`. -/

private theorem realAutocorrelation_tartarV_eq_integral (u : ℝ) :
    realAutocorrelation tartarV u = ∫ t : ℝ, tartarV t * tartarV (t - u) := by
  rw [realAutocorrelation, MeasureTheory.convolution_def]
  simp [reflect, neg_sub]

/-- **Closed form.** For `0 ≤ u ≤ 2`, Tartar's `w = v ⋆ v` is the quintic
`-(1/30) (u ^ 5 - 20 u ^ 3 + 40 u ^ 2 - 32)` (Poitou 1977, §7.2). -/
theorem realAutocorrelation_tartarV_eq {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 2) :
    realAutocorrelation tartarV u
      = -(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32) := by
  have hle : u - 1 ≤ 1 := by linarith
  have hzero : ∀ t : ℝ, t ∉ Set.Icc (u - 1) 1 → tartarV t * tartarV (t - u) = 0 := by
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [tartarV_eq_zero_of_one_le_abs (t := t - u) (le_abs.mpr (Or.inr (by linarith))),
        mul_zero]
    · rw [tartarV_eq_zero_of_one_le_abs (t := t) (le_abs.mpr (Or.inl h.le)), zero_mul]
  have hIcc : ∫ t in Set.Icc (u - 1) 1, tartarV t * tartarV (t - u)
      = ∫ t in Set.Icc (u - 1) 1, (1 - t ^ 2) * (1 - (t - u) ^ 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    rintro t ⟨ht1, ht2⟩
    have e1 : tartarV t = 1 - t ^ 2 := by
      rw [tartarV_apply, max_eq_left]; nlinarith
    have e2 : tartarV (t - u) = 1 - (t - u) ^ 2 := by
      rw [tartarV_apply, max_eq_left]; nlinarith
    simp only [e1, e2]
  have hderiv : ∀ t ∈ Set.uIcc (u - 1) 1,
      HasDerivAt (fun s : ℝ ↦ s ^ 5 / 5 - u / 2 * s ^ 4 + (u ^ 2 - 2) / 3 * s ^ 3
          + u * s ^ 2 + (1 - u ^ 2) * s)
        ((1 - t ^ 2) * (1 - (t - u) ^ 2)) t := by
    intro t _
    have d5 := hasDerivAt_pow 5 t
    have d4 := hasDerivAt_pow 4 t
    have d3 := hasDerivAt_pow 3 t
    have d2 := hasDerivAt_pow 2 t
    have d1 : HasDerivAt (fun x : ℝ ↦ x) 1 t := hasDerivAt_id' (x := t)
    refine HasDerivAt.congr_deriv (HasDerivAt.add (HasDerivAt.add (HasDerivAt.add
      (HasDerivAt.sub (HasDerivAt.div_const d5 5) (HasDerivAt.const_mul (u / 2) d4))
      (HasDerivAt.const_mul ((u ^ 2 - 2) / 3) d3)) (HasDerivAt.const_mul u d2))
      (HasDerivAt.const_mul (1 - u ^ 2) d1)) ?_
    push_cast
    ring
  have hcont : Continuous fun t : ℝ ↦ (1 - t ^ 2) * (1 - (t - u) ^ 2) := by fun_prop
  have hFTC : ∫ t in (u - 1)..1, (1 - t ^ 2) * (1 - (t - u) ^ 2)
      = ((1 : ℝ) ^ 5 / 5 - u / 2 * 1 ^ 4 + (u ^ 2 - 2) / 3 * 1 ^ 3 + u * 1 ^ 2
          + (1 - u ^ 2) * 1)
        - ((u - 1) ^ 5 / 5 - u / 2 * (u - 1) ^ 4 + (u ^ 2 - 2) / 3 * (u - 1) ^ 3
          + u * (u - 1) ^ 2 + (1 - u ^ 2) * (u - 1)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  rw [realAutocorrelation_tartarV_eq_integral,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hIcc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle, hFTC]
  ring

/-- The value of Tartar's `w` at the origin. -/
theorem tartarV_autocorrelation_at_zero : realAutocorrelation tartarV 0 = 16 / 15 := by
  rw [realAutocorrelation_tartarV_eq le_rfl (by norm_num)]
  norm_num

/-! ### Admissibility

The structural inputs of `autocorrelation_isAdmissibleTestFn` are all discharged for
`tartarV`; the two derivative/integrability estimates are *not* — see the module docstring.
They remain explicit hypotheses of the wrapper below. -/

/--
`autocorrelation_isAdmissibleTestFn` specialized to `tartarV`.

All *structural* hypotheses (evenness, continuity, compact support, `LipschitzWith 2`) are
discharged from the lemmas above.  The remaining arguments are the genuine one-dimensional
analytic estimates of the abstract theorem — existence of derivatives for the exponentially
weighted autocorrelation and for the difference quotient, plus their integrability on
`Set.Ici 0` — which this packet deliberately leaves as explicit hypotheses rather than
assuming them.
-/
theorem autocorrelation_tartarV_isAdmissibleTestFn (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (weightedDeriv quotientDeriv : ℝ → ℂ)
    (hweighted_deriv : ∀ x ∈ Set.Ioi 0,
      HasDerivAt (weightedAutocorrelation tartarV epsilon) (weightedDeriv x) x)
    (hweighted_integrable : IntegrableOn weightedDeriv (Set.Ici 0))
    (hquotient_cont : ContinuousOn (autocorrelationDiffQuot tartarV) (Set.Ici 0))
    (hquotient_deriv : ∀ x ∈ Set.Ioi 0,
      HasDerivAt (autocorrelationDiffQuot tartarV) (quotientDeriv x) x)
    (hquotient_integrable : IntegrableOn quotientDeriv (Set.Ici 0)) :
    DedekindResidue.IsAdmissibleTestFn (autocorrelation tartarV) :=
  autocorrelation_isAdmissibleTestFn tartarV 2 tartarV_even continuous_tartarV
    hasCompactSupport_tartarV lipschitzWith_tartarV epsilon hepsilon weightedDeriv quotientDeriv
    hweighted_deriv hweighted_integrable hquotient_cont hquotient_deriv hquotient_integrable

end Odlyzko
