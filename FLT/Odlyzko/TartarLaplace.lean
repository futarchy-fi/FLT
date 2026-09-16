/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouLargeY
public import FLT.Odlyzko.PoitouBoundary
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Laplace transform of Tartar's numerator

This file identifies the elementary Laplace transform underlying Poitou's functions `L` and
`Lclosed`.
-/

@[expose] public section

open MeasureTheory

namespace Odlyzko

private theorem integrable_realAutocorrelation_tartarV :
    Integrable (realAutocorrelation tartarV) := by
  have hc : Integrable (autocorrelation tartarV) :=
    continuous_autocorrelation_tartarV.integrable_of_hasCompactSupport
      hasCompactSupport_autocorrelation_tartarV
  have h := hc.re
  exact h.congr (Filter.Eventually.of_forall fun u ↦ by
    change (autocorrelation tartarV u).re = realAutocorrelation tartarV u
    rw [autocorrelation_eq_ofReal_realAutocorrelation]
    simp)

private theorem continuous_realAutocorrelation_tartarV :
    Continuous (realAutocorrelation tartarV) := by
  exact (Complex.continuous_re.comp continuous_autocorrelation_tartarV).congr (fun u ↦ by
    change (autocorrelation tartarV u).re = realAutocorrelation tartarV u
    rw [autocorrelation_eq_ofReal_realAutocorrelation]
    simp)

private theorem integral_realAutocorrelation_tartarV :
    ∫ u : ℝ, realAutocorrelation tartarV u = 16 / 9 := by
  have hreflect : reflect tartarV = tartarV := by
    funext u
    exact tartarV_even u
  rw [realAutocorrelation, hreflect,
    MeasureTheory.integral_convolution _ integrable_tartarV integrable_tartarV,
    integral_tartarV]
  norm_num [ContinuousLinearMap.lsmul_apply]

private theorem realAutocorrelation_tartarV_even :
    Function.Even (realAutocorrelation tartarV) := by
  intro u
  have h := autocorrelation_tartarV_even u
  rw [autocorrelation_eq_ofReal_realAutocorrelation,
    autocorrelation_eq_ofReal_realAutocorrelation] at h
  exact_mod_cast h

private theorem realAutocorrelation_tartarV_eq_zero_of_two_le_abs {u : ℝ}
    (hu : 2 ≤ |u|) : realAutocorrelation tartarV u = 0 := by
  rw [realAutocorrelation, MeasureTheory.convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases ht : 1 ≤ |t|
  · rw [tartarV_eq_zero_of_one_le_abs ht]
    simp
  · have hut : 1 ≤ |u - t| := by
      have htri : |u| ≤ |u - t| + |t| := by
        calc
          |u| = |u - t + t| := by ring_nf
          _ ≤ |u - t| + |t| := abs_add_le _ _
      linarith
    have hzero : tartarV (-(u - t)) = 0 :=
      tartarV_eq_zero_of_one_le_abs (by simpa only [abs_neg] using hut)
    rw [show reflect tartarV (u - t) = tartarV (-(u - t)) by rfl, hzero]
    simp

/-- The normalized Tartar numerator as a cosine transform of its compactly supported
autocorrelation. -/
theorem tartarNumerator_eq_integral_cos (x : ℝ) :
    tartarNumerator x = 9 / 16 * ∫ u : ℝ,
      realAutocorrelation tartarV u * Real.cos (x * u) := by
  rw [tartarNumerator]
  have hac : autocorrelation tartarV = complexify (realAutocorrelation tartarV) := by
    funext u
    exact autocorrelation_eq_ofReal_realAutocorrelation tartarV u
  rw [hac]
  have h := fourier_complexify_re_eq_integral_cos (realAutocorrelation tartarV)
    integrable_realAutocorrelation_tartarV (-x)
  rw [show x / (2 * Real.pi) = poitouFourierFrequency (-x) by
    rw [poitouFourierFrequency]
    field_simp [show (2 * Real.pi : ℝ) ≠ 0 by positivity]]
  rw [h]
  congr 2
  funext u
  rw [show -x * u = -(x * u) by ring, Real.cos_neg]

/-- The deficit from the normalized value at zero is a nonnegative cosine integral. -/
theorem one_sub_tartarNumerator_eq_integral (x : ℝ) :
    1 - tartarNumerator x = 9 / 16 * ∫ u : ℝ,
      realAutocorrelation tartarV u * (1 - Real.cos (x * u)) := by
  have hcos : Integrable (fun u : ℝ ↦
      realAutocorrelation tartarV u * Real.cos (x * u)) := by
    apply integrable_realAutocorrelation_tartarV.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with u
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x * u)
  rw [tartarNumerator_eq_integral_cos]
  calc
    1 - 9 / 16 * ∫ u : ℝ, realAutocorrelation tartarV u * Real.cos (x * u) =
        9 / 16 * (∫ u : ℝ, realAutocorrelation tartarV u) -
          9 / 16 * ∫ u : ℝ, realAutocorrelation tartarV u * Real.cos (x * u) := by
      rw [integral_realAutocorrelation_tartarV]
      norm_num
    _ = 9 / 16 * ((∫ u : ℝ, realAutocorrelation tartarV u) -
          ∫ u : ℝ, realAutocorrelation tartarV u * Real.cos (x * u)) := by ring
    _ = 9 / 16 * ∫ u : ℝ, (realAutocorrelation tartarV u -
        realAutocorrelation tartarV u * Real.cos (x * u)) := by
      rw [integral_sub integrable_realAutocorrelation_tartarV hcos]
    _ = _ := by
      congr 2
      funext u
      ring

/-- Tartar's normalized numerator is at most one. -/
theorem tartarNumerator_le_one (x : ℝ) : tartarNumerator x ≤ 1 := by
  rw [← sub_nonneg, one_sub_tartarNumerator_eq_integral]
  apply mul_nonneg (by norm_num)
  exact integral_nonneg fun u ↦ mul_nonneg (realAutocorrelation_tartarV_nonneg u)
    (sub_nonneg.mpr (Real.cos_le_one _))

private theorem integral_exp_neg_mul_cos {q : ℝ} (hq : 0 < q) (a : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-q * x) * Real.cos (a * x) =
      q / (q ^ 2 + a ^ 2) := by
  let c : ℂ := (-q : ℝ) + a * Complex.I
  have hc : c.re < 0 := by
    simp only [c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith
  have hint := integrableOn_exp_mul_complex_Ioi hc 0
  have hvalue := congrArg Complex.re (integral_exp_mul_complex_Ioi hc 0)
  have hre : (∫ x in Set.Ioi (0 : ℝ), Complex.exp (c * x)).re =
      ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (c * x)).re :=
    (integral_re hint).symm
  rw [hre] at hvalue
  have hintegrand : (fun x : ℝ ↦ (Complex.exp (c * x)).re) =
      fun x : ℝ ↦ Real.exp (-q * x) * Real.cos (a * x) := by
    funext x
    rw [Complex.exp_re]
    simp only [c, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    congr 2 <;> ring
  rw [hintegrand] at hvalue
  rw [Complex.div_re] at hvalue
  simpa [c, Complex.normSq_apply, pow_two] using hvalue

private theorem integral_exp_neg_mul_one_sub_cos {q : ℝ} (hq : 0 < q) (a : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-q * x) * (1 - Real.cos (a * x)) =
      a ^ 2 / (q * (q ^ 2 + a ^ 2)) := by
  have hexp : IntegrableOn (fun x : ℝ ↦ Real.exp (-q * x)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hcos : IntegrableOn (fun x : ℝ ↦ Real.exp (-q * x) * Real.cos (a * x))
      (Set.Ioi 0) := by
    apply hexp.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with x
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a * x)
  rw [show (fun x : ℝ ↦ Real.exp (-q * x) * (1 - Real.cos (a * x))) =
      fun x ↦ Real.exp (-q * x) - Real.exp (-q * x) * Real.cos (a * x) by
    funext x; ring]
  rw [integral_sub hexp hcos, integral_exp_mul_Ioi (by linarith) 0,
    integral_exp_neg_mul_cos hq]
  simp only [mul_zero, Real.exp_zero]
  field_simp [hq.ne']
  ring

namespace Poitou

private noncomputable def tartarLaplaceIntegrand (y q : ℝ) (p : ℝ × ℝ) : ℝ :=
  realAutocorrelation tartarV p.2 *
    (1 - Real.cos (p.1 * √y * p.2)) * Real.exp (-q * p.1)

private theorem integrable_tartarLaplaceIntegrand {y q : ℝ} (hq : 0 < q) :
    Integrable (tartarLaplaceIntegrand y q)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hexp : Integrable (fun x : ℝ ↦ Real.exp (-q * x))
      (volume.restrict (Set.Ioi 0)) := integrableOn_exp_mul_Ioi (by linarith) 0
  have hbase : Integrable (fun p : ℝ × ℝ ↦
      (2 * Real.exp (-q * p.1)) * realAutocorrelation tartarV p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) :=
    (hexp.const_mul 2).mul_prod integrable_realAutocorrelation_tartarV
  apply hbase.mono'
  · apply Continuous.aestronglyMeasurable
    unfold tartarLaplaceIntegrand
    exact ((continuous_realAutocorrelation_tartarV.comp continuous_snd).mul
      (by fun_prop)).mul (by fun_prop)
  · filter_upwards with p
    simp only [tartarLaplaceIntegrand, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (realAutocorrelation_tartarV_nonneg p.2),
      abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _)),
      abs_of_pos (Real.exp_pos _)]
    have hcos := Real.neg_one_le_cos (p.1 * √y * p.2)
    have hw := realAutocorrelation_tartarV_nonneg p.2
    have he := (Real.exp_pos (-q * p.1)).le
    calc
      realAutocorrelation tartarV p.2 * (1 - Real.cos (p.1 * √y * p.2)) *
          Real.exp (-q * p.1) ≤ realAutocorrelation tartarV p.2 * 2 *
          Real.exp (-q * p.1) := by gcongr; linarith
      _ = 2 * Real.exp (-q * p.1) * realAutocorrelation tartarV p.2 := by ring

private noncomputable def tartarRationalPrimitive (z : ℝ) : ℝ → ℝ :=
  (fun u ↦ -u ^ 6 / 80) +
    (fun u ↦ u ^ 4 * (3 / 8 + 3 / (160 * z))) - (fun u ↦ u ^ 3) -
    (fun u ↦ u ^ 2 * (3 / (4 * z) + 3 / (80 * z ^ 2))) +
    (fun u ↦ u * (12 / 5 + 3 / z)) +
    (fun u ↦ (3 / (80 * z ^ 3) + 3 / (4 * z ^ 2)) * Real.log (1 + z * u ^ 2)) -
    (fun u ↦ (3 / z + 12 / 5) / √z * Real.arctan (u * √z))

private theorem hasDerivAt_tartarRationalPrimitive {z : ℝ} (hz : 0 < z) (u : ℝ) :
    HasDerivAt (tartarRationalPrimitive z)
      (9 / 4 * (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) *
        (z * u ^ 2 / (1 + z * u ^ 2))) u := by
  unfold tartarRationalPrimitive
  have hsqrt : √z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
  have hden : 1 + z * u ^ 2 ≠ 0 := by positivity
  have hlog : HasDerivAt (fun v : ℝ ↦ Real.log (1 + z * v ^ 2))
      ((z * (2 * u)) / (1 + z * u ^ 2)) u := by
    convert ((hasDerivAt_const u 1).add
      ((hasDerivAt_pow 2 u).const_mul z)).log hden using 1
    all_goals simp only [Pi.add_apply]
    all_goals ring
  have hatan : HasDerivAt (fun v : ℝ ↦ Real.arctan (v * √z))
      ((1 / (1 + (u * √z) ^ 2)) * √z) u := by
    convert ((hasDerivAt_id u).mul_const √z).arctan using 1
    all_goals simp only [id_eq]
    all_goals ring
  have h₁ := (hasDerivAt_pow 6 u).neg.div_const 80
  have h₂ := h₁.add ((hasDerivAt_pow 4 u).mul_const (3 / 8 + 3 / (160 * z)))
  have h₃ := h₂.sub (hasDerivAt_pow 3 u)
  have h₄ := h₃.sub
    ((hasDerivAt_pow 2 u).mul_const (3 / (4 * z) + 3 / (80 * z ^ 2)))
  have h₅ := h₄.add ((hasDerivAt_id u).mul_const (12 / 5 + 3 / z))
  have hpoly := h₅.add
    (hlog.const_mul (3 / (80 * z ^ 3) + 3 / (4 * z ^ 2)))
  have h := hpoly.sub (hatan.const_mul ((3 / z + 12 / 5) / √z))
  have h' := h.congr_deriv (g' :=
      9 / 4 * (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) *
        (z * u ^ 2 / (1 + z * u ^ 2))) (by
      rw [show (u * √z) ^ 2 = u ^ 2 * z by rw [mul_pow, Real.sq_sqrt hz.le]]
      field_simp [hz.ne', hsqrt, hden]
      ring)
  exact h'

private theorem integral_tartarRational {z : ℝ} (hz : 0 < z) :
    9 / 4 * ∫ u in Set.Icc (0 : ℝ) 2,
        (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) *
          (z * u ^ 2 / (1 + z * u ^ 2)) = Lclosed z := by
  rw [← integral_const_mul]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (fun u : ℝ ↦ 9 / 4 *
      (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32) *
        (z * u ^ 2 / (1 + z * u ^ 2)))) = fun u : ℝ ↦
      9 / 4 * (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) *
        (z * u ^ 2 / (1 + z * u ^ 2)) by funext u; ring]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_tartarRationalPrimitive hz u)]
  · simp only [tartarRationalPrimitive, Lclosed]
    norm_num [Real.log_one, Real.arctan_zero]
    field_simp [hz.ne', (Real.sqrt_pos.2 hz).ne']
    ring
  · apply Continuous.intervalIntegrable
    have hnum : Continuous (fun u : ℝ ↦ 9 / 4 *
        (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) * (z * u ^ 2)) := by
      fun_prop
    have hden : Continuous (fun u : ℝ ↦ 1 + z * u ^ 2) := by fun_prop
    exact (hnum.div₀ hden (fun u ↦ by positivity)).congr (fun u ↦ by
      field_simp)

private theorem integral_tartarMoment (k : ℕ) :
    9 / 4 * ∫ u in Set.Icc (0 : ℝ) 2,
      (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) * u ^ (2 * k) = c k := by
  rw [← integral_const_mul, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (fun u : ℝ ↦ 9 / 4 *
      ((-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) * u ^ (2 * k))) =
      fun u : ℝ ↦ -3 / 40 *
        (u ^ (2 * k + 5) - 20 * u ^ (2 * k + 3) +
          40 * u ^ (2 * k + 2) - 32 * u ^ (2 * k)) by
    funext u
    simp only [pow_add]
    ring]
  have hp (n : ℕ) : IntervalIntegrable (fun u : ℝ ↦ u ^ n) volume 0 2 :=
    (continuous_pow n).intervalIntegrable _ _
  have hA := hp (2 * k + 5)
  have hB := (hp (2 * k + 3)).const_mul (20 : ℝ)
  have hC := (hp (2 * k + 2)).const_mul (40 : ℝ)
  have hD := (hp (2 * k)).const_mul (32 : ℝ)
  have hAB := hA.sub hB
  have hABC := hAB.add hC
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hABC hD,
    intervalIntegral.integral_add hAB hC,
    intervalIntegral.integral_sub hA hB,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow]
  simp only [zero_pow (by omega : 2 * k + 6 ≠ 0),
    zero_pow (by omega : 2 * k + 4 ≠ 0), zero_pow (by omega : 2 * k + 3 ≠ 0),
    zero_pow (by omega : 2 * k + 1 ≠ 0), sub_zero]
  rw [c, cDen]
  push_cast
  field_simp
  ring

/-- Poitou's closed form agrees with its power series throughout the convergence disc. -/
theorem Lclosed_eq_L {z : ℝ} (hz : 0 < z) (hz4 : z < 1 / 4) : Lclosed z = L z := by
  let w : ℝ → ℝ := fun u ↦
    -(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)
  let F : ℕ → ℝ → ℝ := fun j u ↦
    9 / 4 * w u * ((-1 : ℝ) ^ j * (z * u ^ 2) ^ (j + 1))
  have hFint (j : ℕ) : IntegrableOn (F j) (Set.Icc (0 : ℝ) 2) := by
    apply Continuous.integrableOn_Icc
    unfold F w
    fun_prop
  have hmoment (k : ℕ) :
      ∫ u in Set.Icc (0 : ℝ) 2, 9 / 4 * w u * u ^ (2 * k) = c k := by
    calc
      (∫ u in Set.Icc (0 : ℝ) 2, 9 / 4 * w u * u ^ (2 * k)) =
          9 / 4 * ∫ u in Set.Icc (0 : ℝ) 2, w u * u ^ (2 * k) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with u
        ring
      _ = c k := by
        exact integral_tartarMoment k
  have hterm (j : ℕ) :
      ∫ u in Set.Icc (0 : ℝ) 2, F j u =
        (-1 : ℝ) ^ j * (c (j + 1) * z ^ (j + 1)) := by
    rw [show (fun u : ℝ ↦ F j u) = fun u : ℝ ↦
        ((-1 : ℝ) ^ j * z ^ (j + 1)) *
          (9 / 4 * w u * u ^ (2 * (j + 1))) by
      funext u
      simp only [F, mul_pow, pow_mul]
      ring]
    rw [integral_const_mul]
    rw [show (∫ u in Set.Icc (0 : ℝ) 2, 9 / 4 * w u * u ^ (2 * (j + 1))) =
        c (j + 1) by exact hmoment (j + 1)]
    ring
  have hnorm (j : ℕ) :
      ∫ u in Set.Icc (0 : ℝ) 2, ‖F j u‖ = c (j + 1) * z ^ (j + 1) := by
    have heq : ∀ u ∈ Set.Icc (0 : ℝ) 2,
        ‖F j u‖ = z ^ (j + 1) * (9 / 4 * w u * u ^ (2 * (j + 1))) := by
      intro u hu
      have hw : 0 ≤ w u := by
        rw [show w u = realAutocorrelation tartarV u by
          exact (realAutocorrelation_tartarV_eq hu.1 hu.2).symm]
        exact realAutocorrelation_tartarV_nonneg u
      simp only [F, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul, mul_pow, pow_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4), abs_of_nonneg hw,
        abs_of_nonneg hz.le, sq_abs]
      ring
    rw [setIntegral_congr_fun measurableSet_Icc heq, integral_const_mul]
    rw [show (∫ u in Set.Icc (0 : ℝ) 2, 9 / 4 * w u * u ^ (2 * (j + 1))) =
        c (j + 1) by exact hmoment (j + 1)]
    ring
  have hsumNorm : Summable (fun j : ℕ ↦
      ∫ u in Set.Icc (0 : ℝ) 2, ‖F j u‖) := by
    refine (summable_c_mul_pow hz.le hz4).congr ?_
    intro j
    exact (hnorm j).symm
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumNorm
  have hseries : ∀ u ∈ Set.Icc (0 : ℝ) 2,
      ∑' j : ℕ, F j u = 9 / 4 * w u * (z * u ^ 2 / (1 + z * u ^ 2)) := by
    intro u hu
    have hzu0 : 0 ≤ z * u ^ 2 := mul_nonneg hz.le (sq_nonneg u)
    have hzu4 : z * u ^ 2 < 1 := by
      have hu2 : u ^ 2 ≤ 4 := by nlinarith [hu.1, hu.2]
      nlinarith
    have hgeo := (hasSum_geometric_of_norm_lt_one
      (ξ := -(z * u ^ 2)) (by simpa [abs_of_nonneg hz.le] using hzu4)).mul_left
        (z * u ^ 2)
    have hscalar := hgeo.mul_left (9 / 4 * w u)
    calc
      (∑' j : ℕ, F j u) = ∑' j : ℕ,
          9 / 4 * w u * (z * u ^ 2 * (-(z * u ^ 2)) ^ j) := by
        apply tsum_congr
        intro j
        simp only [F]
        rw [pow_succ', neg_pow]
        ring
      _ = 9 / 4 * w u * (z * u ^ 2 * (1 - -(z * u ^ 2))⁻¹) := hscalar.tsum_eq
      _ = 9 / 4 * w u * (z * u ^ 2 / (1 + z * u ^ 2)) := by
        simp only [sub_neg_eq_add, div_eq_mul_inv]
  calc
    Lclosed z = 9 / 4 * ∫ u in Set.Icc (0 : ℝ) 2,
        w u * (z * u ^ 2 / (1 + z * u ^ 2)) := (integral_tartarRational hz).symm
    _ = ∫ u in Set.Icc (0 : ℝ) 2, ∑' j : ℕ, F j u := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      rw [hseries u hu]
      ring
    _ = ∑' j : ℕ, ∫ u in Set.Icc (0 : ℝ) 2, F j u := hswap.symm
    _ = L z := by
      rw [L]
      apply tsum_congr
      intro j
      exact hterm j

private theorem integral_tartarRational_full {z : ℝ} (hz : 0 < z) :
    9 / 8 * ∫ u : ℝ, realAutocorrelation tartarV u *
      (z * u ^ 2 / (1 + z * u ^ 2)) = Lclosed z := by
  let r : ℝ → ℝ := fun u ↦ realAutocorrelation tartarV u *
    (z * u ^ 2 / (1 + z * u ^ 2))
  have hr_even : Function.Even r := by
    intro u
    simp only [r, neg_sq]
    rw [realAutocorrelation_tartarV_even]
  have habs : (fun u : ℝ ↦ r |u|) = r := by
    funext u
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, hr_even]
  have hhalf := integral_comp_abs (f := r)
  rw [habs] at hhalf
  have hsupport : ∫ u in Set.Ioi (0 : ℝ), r u = ∫ u in Set.Ioc (0 : ℝ) 2, r u := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self
    rintro u ⟨hu0, huout⟩
    have hu0' : 0 < u := Set.mem_Ioi.mp hu0
    have hu2 : 2 ≤ u := by
      by_contra h
      exact huout ⟨hu0', (lt_of_not_ge h).le⟩
    have hu2abs : 2 ≤ |u| := by simpa [abs_of_pos hu0'] using hu2
    simp only [r, realAutocorrelation_tartarV_eq_zero_of_two_le_abs hu2abs, zero_mul]
  rw [hhalf, hsupport, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have heq : (∫ u in Set.Icc (0 : ℝ) 2, r u) = ∫ u in Set.Icc (0 : ℝ) 2,
      (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) *
        (z * u ^ 2 / (1 + z * u ^ 2)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only [r]
    rw [realAutocorrelation_tartarV_eq hu.1 hu.2]
  rw [heq]
  rw [show (9 / 8 : ℝ) * (2 * ∫ u in Set.Icc (0 : ℝ) 2,
      (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) *
        (z * u ^ 2 / (1 + z * u ^ 2))) =
      9 / 4 * ∫ u in Set.Icc (0 : ℝ) 2,
        (-(1 / 30) * (u ^ 5 - 20 * u ^ 3 + 40 * u ^ 2 - 32)) *
          (z * u ^ 2 / (1 + z * u ^ 2)) by ring]
  exact integral_tartarRational hz

/-- The normalized Laplace transform of Tartar's numerator is Poitou's closed form. -/
theorem tartarNumerator_laplace_eq_Lclosed {y q : ℝ} (hy : 0 < y) (hq : 0 < q) :
    2 * ∫ x in Set.Ioi (0 : ℝ),
      (1 - tartarNumerator (x * √y)) * Real.exp (-q * x) =
        q⁻¹ * Lclosed (y / q ^ 2) := by
  have hpoint : ∀ x : ℝ,
      2 * ((1 - tartarNumerator (x * √y)) * Real.exp (-q * x)) =
        9 / 8 * ∫ u : ℝ, tartarLaplaceIntegrand y q (x, u) := by
    intro x
    rw [one_sub_tartarNumerator_eq_integral]
    rw [show (∫ u : ℝ, tartarLaplaceIntegrand y q (x, u)) =
        (∫ u : ℝ, realAutocorrelation tartarV u *
          (1 - Real.cos (x * √y * u))) * Real.exp (-q * x) by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with u
      rfl]
    ring
  have houter :
      2 * ∫ x in Set.Ioi (0 : ℝ),
          (1 - tartarNumerator (x * √y)) * Real.exp (-q * x) =
        9 / 8 * ∫ x in Set.Ioi (0 : ℝ),
          ∫ u : ℝ, tartarLaplaceIntegrand y q (x, u) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    exact hpoint x
  rw [houter]
  have hint : Integrable (Function.uncurry fun x u : ℝ ↦
      tartarLaplaceIntegrand y q (x, u))
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    refine (integrable_tartarLaplaceIntegrand (y := y) hq).congr ?_
    filter_upwards with p
    rfl
  have hswap := integral_integral_swap hint
  change (∫ x in Set.Ioi (0 : ℝ), ∫ u : ℝ, tartarLaplaceIntegrand y q (x, u)) =
      ∫ u : ℝ, ∫ x in Set.Ioi (0 : ℝ), tartarLaplaceIntegrand y q (x, u) at hswap
  rw [hswap]
  have hinner : (fun u : ℝ ↦ ∫ x in Set.Ioi (0 : ℝ),
      tartarLaplaceIntegrand y q (x, u)) = fun u : ℝ ↦
        q⁻¹ * (realAutocorrelation tartarV u *
          ((y / q ^ 2) * u ^ 2 / (1 + (y / q ^ 2) * u ^ 2))) := by
    funext u
    calc
      (∫ x in Set.Ioi (0 : ℝ), tartarLaplaceIntegrand y q (x, u)) =
          realAutocorrelation tartarV u *
            ∫ x in Set.Ioi (0 : ℝ), Real.exp (-q * x) *
              (1 - Real.cos ((√y * u) * x)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        simp only [tartarLaplaceIntegrand]
        rw [show x * √y * u = (√y * u) * x by ring]
        ring
      _ = realAutocorrelation tartarV u *
          ((√y * u) ^ 2 / (q * (q ^ 2 + (√y * u) ^ 2))) := by
        rw [integral_exp_neg_mul_one_sub_cos hq]
      _ = q⁻¹ * (realAutocorrelation tartarV u *
          ((y / q ^ 2) * u ^ 2 / (1 + (y / q ^ 2) * u ^ 2))) := by
        rw [show (√y * u) ^ 2 = y * u ^ 2 by rw [mul_pow, Real.sq_sqrt hy.le]]
        field_simp [hq.ne']
  rw [hinner, integral_const_mul]
  rw [show (fun u : ℝ ↦ realAutocorrelation tartarV u *
      ((y / q ^ 2) * u ^ 2 / (1 + (y / q ^ 2) * u ^ 2))) = fun u : ℝ ↦
      realAutocorrelation tartarV u *
        ((y / q ^ 2) * u ^ 2 / (1 + (y / q ^ 2) * u ^ 2)) by rfl]
  rw [show 9 / 8 * (q⁻¹ * ∫ u : ℝ, realAutocorrelation tartarV u *
      ((y / q ^ 2) * u ^ 2 / (1 + (y / q ^ 2) * u ^ 2))) =
      q⁻¹ * (9 / 8 * ∫ u : ℝ, realAutocorrelation tartarV u *
        ((y / q ^ 2) * u ^ 2 / (1 + (y / q ^ 2) * u ^ 2))) by ring]
  rw [integral_tartarRational_full (div_pos hy (sq_pos_of_pos hq))]

/-- Inside the convergence disc, the same Laplace transform is Poitou's power series. -/
theorem tartarNumerator_laplace_eq_L {y q : ℝ} (hy : 0 < y) (hq : 0 < q)
    (hscaled : y / q ^ 2 < 1 / 4) :
    2 * ∫ x in Set.Ioi (0 : ℝ),
      (1 - tartarNumerator (x * √y)) * Real.exp (-q * x) =
        q⁻¹ * L (y / q ^ 2) := by
  calc
    2 * ∫ x in Set.Ioi (0 : ℝ),
        (1 - tartarNumerator (x * √y)) * Real.exp (-q * x) =
          q⁻¹ * Lclosed (y / q ^ 2) := tartarNumerator_laplace_eq_Lclosed hy hq
    _ = q⁻¹ * L (y / q ^ 2) := by
      rw [Lclosed_eq_L (div_pos hy (sq_pos_of_pos hq)) hscaled]

end Poitou

end Odlyzko
