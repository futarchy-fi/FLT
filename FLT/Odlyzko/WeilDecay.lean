/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.WeilAdapter

/-!
# Decay estimates for Gaussian Tartar approximants

This file proves the two derivatives needed to integrate the Fourier transform of a
Gaussian Tartar approximant by parts.  The estimates are uniform for exponential tilts
`|q| ≤ 3/4`, covering the closed Weil strip at band width `1/8`.
-/

@[expose] public section

open Complex Filter MeasureTheory
open scoped ENNReal NNReal FourierTransform Topology ContDiff

namespace Odlyzko

open Module NumberField

private theorem exists_bounds_deriv_fourier_autocorrelation_tartarV :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ x : ℝ, ‖deriv (𝓕 (autocorrelation tartarV)) x‖ ≤ C₁) ∧
      (∀ x : ℝ, ‖deriv (deriv (𝓕 (autocorrelation tartarV))) x‖ ≤ C₂) := by
  let H : ℝ → ℂ := 𝓕 (autocorrelation tartarV)
  let C (k : ℕ) : ℝ :=
    (2 * Real.pi) ^ k *
      ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range 1,
        ∫ v : ℝ, ‖v‖ ^ p.1 *
          ‖iteratedFDeriv ℝ p.2 (autocorrelation tartarV) v‖
  have hsource : ContDiff ℝ 0 (autocorrelation tartarV) :=
    contDiff_zero.mpr continuous_autocorrelation_tartarV
  have hmoments (k n : ℕ) (_hk : (k : ℕ∞) ≤ 2) (hn : (n : ℕ∞) ≤ 0) :
      Integrable (fun v : ℝ => ‖v‖ ^ k *
        ‖iteratedFDeriv ℝ n (autocorrelation tartarV) v‖) := by
    have hnle : n ≤ 0 := by exact_mod_cast hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnle
    subst n
    simpa using integrable_norm_pow_mul_norm_autocorrelation_tartarV k
  have hbound (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
      ‖iteratedDeriv k H x‖ ≤ C k := by
    have hraw := Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := (2 : ℕ∞)) (N := (0 : ℕ∞)) hsource hmoments
      (k := k) (n := 0) (by exact_mod_cast hk) (by simp) x
    have heval :
        ‖iteratedDeriv k H x‖ ≤ ‖iteratedFDeriv ℝ k H x‖ := by
      rw [iteratedDeriv_eq_iteratedFDeriv]
      exact (ContinuousMultilinearMap.le_opNorm
        (iteratedFDeriv ℝ k H x) (fun _ => 1)).trans_eq (by simp)
    exact heval.trans (by simpa [C, H] using hraw)
  refine ⟨C 1, C 2, ?_, ?_, ?_, ?_⟩
  · dsimp [C]
    positivity
  · dsimp [C]
    positivity
  · intro x
    simpa [H, iteratedDeriv_succ] using hbound 1 (by norm_num) x
  · intro x
    simpa [H, iteratedDeriv_succ] using hbound 2 (by norm_num) x

private theorem exists_bounds_deriv_tartarNumerator :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ x : ℝ, ‖deriv tartarNumerator x‖ ≤ C₁) ∧
      (∀ x : ℝ, ‖deriv (deriv tartarNumerator) x‖ ≤ C₂) := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hb₁, hb₂⟩ :=
    exists_bounds_deriv_fourier_autocorrelation_tartarV
  let H : ℝ → ℂ := 𝓕 (autocorrelation tartarV)
  have hH : ContDiff ℝ ∞ H := contDiff_fourier_autocorrelation_tartarV
  have hH' : ContDiff ℝ ∞ (deriv H) := (contDiff_infty_iff_deriv.mp hH).2
  have hformula₁ : deriv tartarNumerator = fun x : ℝ =>
      9 / 16 * (deriv H (x / (2 * Real.pi))).re / (2 * Real.pi) := by
    funext x
    have hinner : HasDerivAt
        (fun u : ℝ => (H (u / (2 * Real.pi))).re)
        ((deriv H (x / (2 * Real.pi))).re / (2 * Real.pi)) x := by
      have hbase : HasDerivAt (fun u : ℝ => (H u).re)
          (deriv H (x / (2 * Real.pi))).re (x / (2 * Real.pi)) :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt _
          ((hH.differentiable (by simp)) _).hasDerivAt
      have hcomp := hbase.comp x ((hasDerivAt_id x).div_const (2 * Real.pi))
      refine (hcomp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv ?_
      ring
    have h := hinner.const_mul (9 / 16)
    have heq : tartarNumerator =
        fun u : ℝ => 9 / 16 * (H (u / (2 * Real.pi))).re := by
      funext u
      rfl
    rw [← heq] at h
    simpa [div_eq_mul_inv, mul_assoc] using h.deriv
  have hformula₂ : deriv (deriv tartarNumerator) = fun x : ℝ =>
      9 / 16 * (deriv (deriv H) (x / (2 * Real.pi))).re /
        (2 * Real.pi) ^ 2 := by
    rw [hformula₁]
    funext x
    have hinner : HasDerivAt
        (fun u : ℝ => (deriv H (u / (2 * Real.pi))).re)
        ((deriv (deriv H) (x / (2 * Real.pi))).re / (2 * Real.pi)) x := by
      have hbase : HasDerivAt (fun u : ℝ => (deriv H u).re)
          (deriv (deriv H) (x / (2 * Real.pi))).re (x / (2 * Real.pi)) :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt _
          ((hH'.differentiable (by simp)) _).hasDerivAt
      have hcomp := hbase.comp x ((hasDerivAt_id x).div_const (2 * Real.pi))
      refine (hcomp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv ?_
      ring
    have h := (hinner.const_mul (9 / 16)).div_const (2 * Real.pi)
    convert h.deriv using 1
    all_goals ring
  refine ⟨9 / 16 / (2 * Real.pi) * D₁,
    9 / 16 / (2 * Real.pi) ^ 2 * D₂, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro x
    rw [hformula₁, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 16),
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    calc
      9 / 16 * |(deriv H (x / (2 * Real.pi))).re| / (2 * Real.pi)
          ≤ 9 / 16 * ‖deriv H (x / (2 * Real.pi))‖ / (2 * Real.pi) := by
            gcongr
            exact Complex.abs_re_le_norm _
      _ ≤ 9 / 16 / (2 * Real.pi) * D₁ := by
        have hc : 0 ≤ 9 / 16 / (2 * Real.pi) := by positivity
        calc
          9 / 16 * ‖deriv H (x / (2 * Real.pi))‖ / (2 * Real.pi) =
              (9 / 16 / (2 * Real.pi)) *
                ‖deriv H (x / (2 * Real.pi))‖ := by ring
          _ ≤ (9 / 16 / (2 * Real.pi)) * D₁ :=
            mul_le_mul_of_nonneg_left (hb₁ _) hc
  · intro x
    rw [hformula₂, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 16),
      abs_pow, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    calc
      9 / 16 * |(deriv (deriv H) (x / (2 * Real.pi))).re| /
            (2 * Real.pi) ^ 2
          ≤ 9 / 16 * ‖deriv (deriv H) (x / (2 * Real.pi))‖ /
            (2 * Real.pi) ^ 2 := by
              gcongr
              exact Complex.abs_re_le_norm _
      _ ≤ 9 / 16 / (2 * Real.pi) ^ 2 * D₂ := by
        have hc : 0 ≤ 9 / 16 / (2 * Real.pi) ^ 2 := by positivity
        calc
          9 / 16 * ‖deriv (deriv H) (x / (2 * Real.pi))‖ /
              (2 * Real.pi) ^ 2 =
              (9 / 16 / (2 * Real.pi) ^ 2) *
                ‖deriv (deriv H) (x / (2 * Real.pi))‖ := by ring
          _ ≤ (9 / 16 / (2 * Real.pi) ^ 2) * D₂ :=
            mul_le_mul_of_nonneg_left (hb₂ _) hc

private theorem exists_bounds_deriv_scaledTartarNumerator
    {a : ℝ} (ha : 0 < a) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ x : ℝ, ‖deriv (scaledNumerator tartarNumerator a) x‖ ≤ C₁) ∧
      (∀ x : ℝ, ‖deriv (deriv
        (scaledNumerator tartarNumerator a)) x‖ ≤ C₂) := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hb₁, hb₂⟩ := exists_bounds_deriv_tartarNumerator
  let f := scaledNumerator tartarNumerator a
  have hbase : ContDiff ℝ ∞ tartarNumerator := contDiff_tartarNumerator
  have hbase' : ContDiff ℝ ∞ (deriv tartarNumerator) :=
    (contDiff_infty_iff_deriv.mp hbase).2
  have hformula₁ : deriv f = fun x : ℝ => deriv tartarNumerator (x / a) / a := by
    funext x
    have h := ((hbase.differentiable (by simp)) (x / a)).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const a)
    have hfder : HasDerivAt f
        (deriv tartarNumerator (x / a) * (1 / a)) x := by
      refine (h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun u => ?_))).congr_deriv rfl
      rfl
    simpa [div_eq_mul_inv] using hfder.deriv
  have hformula₂ : deriv (deriv f) =
      fun x : ℝ => deriv (deriv tartarNumerator) (x / a) / a ^ 2 := by
    rw [hformula₁]
    funext x
    have h := ((hbase'.differentiable (by simp)) (x / a)).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const a)
    have h' := h.div_const a
    have hderiv := h'.deriv
    simpa only [Function.comp_apply, id_eq, div_eq_mul_inv] using
      hderiv.trans (by field_simp [ha.ne'])
  refine ⟨D₁ / a, D₂ / a ^ 2, by positivity, by positivity, ?_, ?_⟩
  · intro x
    rw [hformula₁, norm_div]
    simpa [Real.norm_eq_abs, abs_of_pos ha] using
      div_le_div_of_nonneg_right (hb₁ (x / a)) ha.le
  · intro x
    rw [hformula₂, norm_div]
    simpa [Real.norm_eq_abs, abs_of_pos ha, abs_pow] using
      div_le_div_of_nonneg_right (hb₂ (x / a)) (sq_nonneg a)

private theorem integrable_one_add_abs_sq_mul_gaussian
    (c : ℝ) (hc : 0 < c) (q : ℝ) :
    Integrable (fun x : ℝ =>
      (1 + |x|) ^ 2 * Real.exp (-x ^ 2 / c + |q| * |x|)) := by
  let b : ℝ := 1 / (2 * c)
  have hb : 0 < b := by dsimp [b]; positivity
  have h0 : Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have h1 : Integrable (fun x : ℝ => |x| * Real.exp (-b * x ^ 2)) := by
    have h := (integrable_mul_exp_neg_mul_sq hb).norm
    convert h using 1
    funext x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) := by
    simpa [Real.rpow_two, sq_abs] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2))
  have hpoly : Integrable (fun x : ℝ =>
      Real.exp (c * q ^ 2 / 2) *
        (Real.exp (-b * x ^ 2) +
          2 * (|x| * Real.exp (-b * x ^ 2)) +
          x ^ 2 * Real.exp (-b * x ^ 2))) :=
    (h0.add (h1.const_mul 2) |>.add h2).const_mul _
  refine Integrable.mono' hpoly (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hexponent :
      -x ^ 2 / c + |q| * |x| ≤ -b * x ^ 2 + c * q ^ 2 / 2 := by
    dsimp [b]
    have hsquare : 0 ≤ (|x| - c * |q|) ^ 2 := sq_nonneg _
    have habssq : |x| ^ 2 = x ^ 2 := sq_abs x
    have habssq_q : |q| ^ 2 = q ^ 2 := sq_abs q
    field_simp [hc.ne']
    nlinarith [abs_nonneg q, habssq, habssq_q]
  have hexp := Real.exp_le_exp.mpr hexponent
  calc
    (1 + |x|) ^ 2 * Real.exp (-x ^ 2 / c + |q| * |x|)
        ≤ (1 + |x|) ^ 2 *
            Real.exp (-b * x ^ 2 + c * q ^ 2 / 2) := by gcongr
    _ = Real.exp (c * q ^ 2 / 2) *
        (Real.exp (-b * x ^ 2) +
          2 * (|x| * Real.exp (-b * x ^ 2)) +
          x ^ 2 * Real.exp (-b * x ^ 2)) := by
      rw [Real.exp_add]
      ring_nf
      rw [sq_abs]

/-- The Gaussian/cosh weight after tilting a Poitou approximant by `exp (q * x)`. -/
noncomputable def weilGaussianWeight (n : ℕ) (q x : ℝ) : ℝ :=
  poitouGaussianCutoff n x / Real.cosh (x / 2) * Real.exp (q * x)

private noncomputable def weilGaussianLogDeriv (n : ℕ) (q x : ℝ) : ℝ :=
  -2 * x / ((n : ℝ) + 1) - Real.tanh (x / 2) / 2 + q

private theorem hasDerivAt_poitouGaussianCutoff' (n : ℕ) (x : ℝ) :
    HasDerivAt (poitouGaussianCutoff n)
      (-2 * x / ((n : ℝ) + 1) * poitouGaussianCutoff n x) x := by
  have hinner : HasDerivAt (fun u : ℝ ↦ -u ^ 2 / ((n : ℝ) + 1))
      (-2 * x / ((n : ℝ) + 1)) x := by
    have h := ((hasDerivAt_id x).pow 2).neg.div_const ((n : ℝ) + 1)
    refine h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u ↦ by simp only [id_eq, Pi.pow_apply, Pi.neg_apply]))
      |>.congr_deriv ?_
    norm_num
  unfold poitouGaussianCutoff
  refine hinner.exp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun _ ↦ rfl)) |>.congr_deriv ?_
  ring

private theorem hasDerivAt_tanh_half (x : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.tanh (u / 2))
      (1 / (2 * Real.cosh (x / 2) ^ 2)) x := by
  have hinner : HasDerivAt (fun u : ℝ ↦ u / 2) (1 / 2) x := by
    have h := (hasDerivAt_id x).div_const 2
    refine h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u ↦ by simp only [id_eq]))
      |>.congr_deriv ?_
    rfl
  have hsinh := hinner.sinh
  have hcosh := hinner.cosh
  have h := hsinh.div hcosh (Real.cosh_pos (x / 2)).ne'
  rw [show (fun u : ℝ ↦ Real.tanh (u / 2)) =
      fun u : ℝ ↦ Real.sinh (u / 2) / Real.cosh (u / 2) by
    funext u
    exact Real.tanh_eq_sinh_div_cosh _]
  convert h using 1
  all_goals first | rfl |
    (field_simp [(Real.cosh_pos (x / 2)).ne']; nlinarith [Real.cosh_sq (x / 2)])

private theorem hasDerivAt_weilGaussianLogDeriv (n : ℕ) (q x : ℝ) :
    HasDerivAt (weilGaussianLogDeriv n q)
      (-2 / ((n : ℝ) + 1) - 1 / (4 * Real.cosh (x / 2) ^ 2)) x := by
  unfold weilGaussianLogDeriv
  have hlinear : HasDerivAt (fun u : ℝ ↦ -2 * u / ((n : ℝ) + 1))
      (-2 / ((n : ℝ) + 1)) x := by
    have h := ((hasDerivAt_id x).const_mul (-2)).div_const ((n : ℝ) + 1)
    refine h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u ↦ by simp only [id_eq]))
      |>.congr_deriv ?_
    ring
  have htanh := (hasDerivAt_tanh_half x).div_const 2
  convert (hlinear.sub htanh).add_const q using 1
  all_goals first | rfl | ring

private theorem hasDerivAt_weilGaussianWeight (n : ℕ) (q x : ℝ) :
    HasDerivAt (weilGaussianWeight n q)
      (weilGaussianWeight n q x * weilGaussianLogDeriv n q x) x := by
  have hcosh : HasDerivAt (fun u : ℝ ↦ Real.cosh (u / 2))
      (Real.sinh (x / 2) / 2) x := by
    simpa only [id_eq, div_eq_mul_inv, one_mul] using
      ((hasDerivAt_id x).div_const 2).cosh
  have hquot := (hasDerivAt_poitouGaussianCutoff' n x).div hcosh
    (Real.cosh_pos (x / 2)).ne'
  have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (q * u))
      (q * Real.exp (q * x)) x := by
    have hinner := (hasDerivAt_id x).const_mul q
    refine hinner.exp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u ↦ by simp only [id_eq]))
      |>.congr_deriv ?_
    simp only [id_eq]
    ring
  have h := hquot.mul hexp
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ ↦ rfl))
    |>.congr_deriv ?_
  rw [weilGaussianWeight, weilGaussianLogDeriv, Real.tanh_eq_sinh_div_cosh]
  simp only [Pi.div_apply]
  field_simp [(Real.cosh_pos (x / 2)).ne']

private theorem hasDerivAt_deriv_weilGaussianWeight (n : ℕ) (q x : ℝ) :
    HasDerivAt (deriv (weilGaussianWeight n q))
      (weilGaussianWeight n q x *
        (weilGaussianLogDeriv n q x ^ 2
          - 2 / ((n : ℝ) + 1) - 1 / (4 * Real.cosh (x / 2) ^ 2))) x := by
  have hformula : deriv (weilGaussianWeight n q) =
      fun u : ℝ ↦ weilGaussianWeight n q u * weilGaussianLogDeriv n q u := by
    funext u
    exact (hasDerivAt_weilGaussianWeight n q u).deriv
  rw [hformula]
  convert (hasDerivAt_weilGaussianWeight n q x).mul
    (hasDerivAt_weilGaussianLogDeriv n q x) using 1
  all_goals first | rfl | ring

private theorem weilGaussianWeight_nonneg (n : ℕ) (q x : ℝ) :
    0 ≤ weilGaussianWeight n q x := by
  unfold weilGaussianWeight
  exact mul_nonneg
    (div_nonneg (poitouGaussianCutoff_pos n x).le (Real.cosh_pos _).le)
    (Real.exp_pos _).le

private theorem weilGaussianWeight_le (n : ℕ) (q x : ℝ) :
    weilGaussianWeight n q x ≤
      Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) := by
  unfold weilGaussianWeight
  have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
  have hcut : 0 ≤ poitouGaussianCutoff n x := (poitouGaussianCutoff_pos n x).le
  calc
    poitouGaussianCutoff n x / Real.cosh (x / 2) * Real.exp (q * x)
        ≤ poitouGaussianCutoff n x * Real.exp (q * x) := by
          gcongr
          exact div_le_self hcut hcosh
    _ = Real.exp (-x ^ 2 / ((n : ℝ) + 1) + q * x) := by
      rw [poitouGaussianCutoff, ← Real.exp_add]
    _ ≤ Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [le_abs_self q, le_abs_self x, neg_le_abs q, neg_le_abs x,
        abs_nonneg q, abs_nonneg x, abs_mul q x]

private theorem norm_weilGaussianLogDeriv_le (n : ℕ) {q : ℝ}
    (hq : |q| ≤ 3 / 4) (x : ℝ) :
    ‖weilGaussianLogDeriv n q x‖ ≤ 2 * (1 + |x|) := by
  rw [Real.norm_eq_abs]
  unfold weilGaussianLogDeriv
  have hc : 1 ≤ (n : ℝ) + 1 := by norm_num
  have htanh : |Real.tanh (x / 2)| ≤ 1 := (Real.abs_tanh_lt_one _).le
  calc
    |-2 * x / ((n : ℝ) + 1) - Real.tanh (x / 2) / 2 + q|
        ≤ 2 * |x| / ((n : ℝ) + 1) + |Real.tanh (x / 2)| / 2 + |q| := by
          calc
            _ ≤ |-2 * x / ((n : ℝ) + 1)| + |Real.tanh (x / 2) / 2| + |q| := by
              rw [show -2 * x / ((n : ℝ) + 1) - Real.tanh (x / 2) / 2 + q =
                (-2 * x / ((n : ℝ) + 1) - Real.tanh (x / 2) / 2) + q by ring]
              exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
            _ = _ := by
              rw [abs_div, abs_mul, abs_neg, abs_div,
                abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
              norm_num
    _ ≤ 2 * |x| + 1 / 2 + 3 / 4 := by
      gcongr
      exact div_le_self (by positivity) hc
    _ ≤ 2 * (1 + |x|) := by linarith

private theorem norm_deriv_weilGaussianLogDeriv_le (n : ℕ) (_q x : ℝ) :
    ‖-2 / ((n : ℝ) + 1) - 1 / (4 * Real.cosh (x / 2) ^ 2)‖ ≤ 3 := by
  have hneg : -2 / ((n : ℝ) + 1) - 1 / (4 * Real.cosh (x / 2) ^ 2) ≤ 0 := by
    have hleft : -2 / ((n : ℝ) + 1) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    have hright : 0 ≤ 1 / (4 * Real.cosh (x / 2) ^ 2) := by positivity
    linarith
  rw [Real.norm_eq_abs, abs_of_nonpos hneg]
  have hc : 1 ≤ (n : ℝ) + 1 := by norm_num
  have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
  have hcoshsq : 1 ≤ Real.cosh (x / 2) ^ 2 := by nlinarith
  have h1 : 2 / ((n : ℝ) + 1) ≤ 2 := by
    exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2 (by nlinarith)
  have h2 : 1 / (4 * Real.cosh (x / 2) ^ 2) ≤ 1 / 4 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have heq : -(-2 / ((n : ℝ) + 1) - 1 / (4 * Real.cosh (x / 2) ^ 2)) =
      2 / ((n : ℝ) + 1) + 1 / (4 * Real.cosh (x / 2) ^ 2) := by ring
  rw [heq]
  linarith

private theorem norm_deriv_weilGaussianWeight_le (n : ℕ) {q : ℝ}
    (hq : |q| ≤ 3 / 4) (x : ℝ) :
    ‖deriv (weilGaussianWeight n q) x‖ ≤
      2 * (1 + |x|) *
        Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) := by
  rw [(hasDerivAt_weilGaussianWeight n q x).deriv, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (weilGaussianWeight_nonneg n q x)]
  exact mul_le_mul (weilGaussianWeight_le n q x)
    (norm_weilGaussianLogDeriv_le n hq x) (norm_nonneg _)
    (Real.exp_pos _).le |>.trans_eq (by ring)

private theorem norm_deriv_deriv_weilGaussianWeight_le (n : ℕ) {q : ℝ}
    (hq : |q| ≤ 3 / 4) (x : ℝ) :
    ‖deriv (deriv (weilGaussianWeight n q)) x‖ ≤
      7 * (1 + |x|) ^ 2 *
        Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) := by
  rw [(hasDerivAt_deriv_weilGaussianWeight n q x).deriv, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (weilGaussianWeight_nonneg n q x)]
  have hlog := norm_weilGaussianLogDeriv_le n hq x
  have hlog' := norm_deriv_weilGaussianLogDeriv_le n q x
  have hx : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hin :
      ‖weilGaussianLogDeriv n q x ^ 2 - 2 / ((n : ℝ) + 1) -
          1 / (4 * Real.cosh (x / 2) ^ 2)‖ ≤
        ‖weilGaussianLogDeriv n q x‖ ^ 2 + 3 := by
    rw [show weilGaussianLogDeriv n q x ^ 2 - 2 / ((n : ℝ) + 1) -
        1 / (4 * Real.cosh (x / 2) ^ 2) =
      weilGaussianLogDeriv n q x ^ 2 +
        (-2 / ((n : ℝ) + 1) - 1 / (4 * Real.cosh (x / 2) ^ 2)) by ring]
    exact (norm_add_le _ _).trans (add_le_add (norm_pow_le _ _) hlog')
  calc
    weilGaussianWeight n q x *
        ‖weilGaussianLogDeriv n q x ^ 2 - 2 / ((n : ℝ) + 1) -
          1 / (4 * Real.cosh (x / 2) ^ 2)‖
        ≤ weilGaussianWeight n q x *
            (‖weilGaussianLogDeriv n q x‖ ^ 2 + 3) := by
          exact mul_le_mul_of_nonneg_left hin (weilGaussianWeight_nonneg n q x)
    _ ≤ Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) *
          ((2 * (1 + |x|)) ^ 2 + 3) := by
          exact mul_le_mul (weilGaussianWeight_le n q x)
            (add_le_add ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hlog) (le_refl 3))
            (by positivity) (Real.exp_pos _).le
    _ ≤ 7 * (1 + |x|) ^ 2 *
          Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) := by
          have hcoef : (2 * (1 + |x|)) ^ 2 + 3 ≤
              7 * (1 + |x|) ^ 2 := by nlinarith
          calc
            Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) *
                ((2 * (1 + |x|)) ^ 2 + 3) =
                ((2 * (1 + |x|)) ^ 2 + 3) *
                  Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) := by ring
            _ ≤ 7 * (1 + |x|) ^ 2 *
                Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) :=
              mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

/-- A Gaussian Tartar approximant tilted by `exp (q * x)`. -/
noncomputable def weilGaussianSymbol (a : ℝ) (n : ℕ) (q x : ℝ) : ℂ :=
  ((scaledNumerator tartarNumerator a x * weilGaussianWeight n q x : ℝ) : ℂ)

theorem weilGaussianSymbol_eq (a : ℝ) (n : ℕ) (q x : ℝ) :
    weilGaussianSymbol a n q x =
      gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n x *
        ((Real.exp (q * x) : ℝ) : ℂ) := by
  rw [weilGaussianSymbol, weilGaussianWeight, gaussianPoitouApproximant,
    poitouKernel_apply]
  unfold gaussianDampedNumerator
  push_cast
  ring

private theorem hasDerivAt_weilGaussianSymbol (a : ℝ) (n : ℕ) (q x : ℝ) :
    HasDerivAt (weilGaussianSymbol a n q)
      ((deriv (scaledNumerator tartarNumerator a) x * weilGaussianWeight n q x +
        scaledNumerator tartarNumerator a x * deriv (weilGaussianWeight n q) x : ℝ) : ℂ) x := by
  unfold weilGaussianSymbol
  have h := (((contDiff_scaledTartarNumerator a).differentiable (by simp) x).hasDerivAt.mul
    (hasDerivAt_weilGaussianWeight n q x)).ofReal_comp
  convert h using 1
  all_goals first | rfl | rw [(hasDerivAt_weilGaussianWeight n q x).deriv]

private theorem hasDerivAt_deriv_weilGaussianSymbol (a : ℝ) (n : ℕ) (q x : ℝ) :
    HasDerivAt (deriv (weilGaussianSymbol a n q))
      ((deriv (deriv (scaledNumerator tartarNumerator a)) x * weilGaussianWeight n q x +
        2 * deriv (scaledNumerator tartarNumerator a) x *
          deriv (weilGaussianWeight n q) x +
        scaledNumerator tartarNumerator a x *
          deriv (deriv (weilGaussianWeight n q)) x : ℝ) : ℂ) x := by
  have hformula : deriv (weilGaussianSymbol a n q) = fun u : ℝ =>
      ((deriv (scaledNumerator tartarNumerator a) u * weilGaussianWeight n q u +
        scaledNumerator tartarNumerator a u * deriv (weilGaussianWeight n q) u : ℝ) : ℂ) := by
    funext u
    exact (hasDerivAt_weilGaussianSymbol a n q u).deriv
  rw [hformula]
  have hf' := ((contDiff_infty_iff_deriv.mp
    (contDiff_scaledTartarNumerator a)).2.differentiable (by simp) x).hasDerivAt
  have hf := ((contDiff_scaledTartarNumerator a).differentiable (by simp) x).hasDerivAt
  have hW : HasDerivAt (weilGaussianWeight n q)
      (deriv (weilGaussianWeight n q) x) x := by
    convert hasDerivAt_weilGaussianWeight n q x using 1
    exact (hasDerivAt_weilGaussianWeight n q x).deriv
  have hW' : HasDerivAt (deriv (weilGaussianWeight n q))
      (deriv (deriv (weilGaussianWeight n q)) x) x := by
    convert hasDerivAt_deriv_weilGaussianWeight n q x using 1
    exact (hasDerivAt_deriv_weilGaussianWeight n q x).deriv
  convert ((hf'.mul hW).add (hf.mul hW')).ofReal_comp using 1
  · rfl
  · push_cast
    ring

private theorem integrable_weilGaussian_majorant (n : ℕ) (q : ℝ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ 2 *
      Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)) :=
  integrable_one_add_abs_sq_mul_gaussian ((n : ℝ) + 1) (by positivity) q

theorem integrable_weilGaussianSymbol_deriv_two
    {a : ℝ} (ha : 0 < a) (n : ℕ) {q : ℝ} (hq : |q| ≤ 3 / 4) :
    Integrable (weilGaussianSymbol a n q) ∧
      Integrable (deriv (weilGaussianSymbol a n q)) ∧
      Integrable (deriv (deriv (weilGaussianSymbol a n q))) := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hb₁, hb₂⟩ :=
    exists_bounds_deriv_scaledTartarNumerator ha
  let M : ℝ → ℝ := fun x => (1 + |x|) ^ 2 *
    Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)
  have hM : Integrable M := integrable_weilGaussian_majorant n q
  have hsymbol_cont : Continuous (weilGaussianSymbol a n q) :=
    continuous_iff_continuousAt.2 (fun x =>
      (hasDerivAt_weilGaussianSymbol a n q x).continuousAt)
  have hM0 (x : ℝ) : Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤ M x := by
    dsimp [M]
    have : 1 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
    exact (le_mul_iff_one_le_left (Real.exp_pos _)).2 this
  constructor
  · refine Integrable.mono' hM hsymbol_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [weilGaussianSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (weilGaussianWeight_nonneg n q x)]
    unfold scaledNumerator
    rw [abs_of_nonneg (tartarNumerator_nonneg (x / a))]
    exact (mul_le_of_le_one_left (weilGaussianWeight_nonneg n q x)
      (tartarNumerator_le_one (x / a))).trans
        ((weilGaussianWeight_le n q x).trans (hM0 x))
  constructor
  · refine Integrable.mono' (hM.const_mul (D₁ + 2)) (by fun_prop)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [(hasDerivAt_weilGaussianSymbol a n q x).deriv, Complex.norm_real,
      Real.norm_eq_abs]
    have hf0 : |scaledNumerator tartarNumerator a x| ≤ 1 := by
      unfold scaledNumerator
      rw [abs_of_nonneg (tartarNumerator_nonneg (x / a))]
      exact tartarNumerator_le_one _
    have hW := weilGaussianWeight_le n q x
    have hW' := norm_deriv_weilGaussianWeight_le n hq x
    have hbase0 := hM0 x
    have hbase1 : (1 + |x|) *
        Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤ M x := by
      dsimp [M]
      have hx : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
      nlinarith [Real.exp_pos (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)]
    calc
      |deriv (scaledNumerator tartarNumerator a) x * weilGaussianWeight n q x +
          scaledNumerator tartarNumerator a x * deriv (weilGaussianWeight n q) x|
          ≤ ‖deriv (scaledNumerator tartarNumerator a) x‖ * weilGaussianWeight n q x +
              |scaledNumerator tartarNumerator a x| *
                ‖deriv (weilGaussianWeight n q) x‖ := by
            simpa [abs_mul, Real.norm_eq_abs,
              abs_of_nonneg (weilGaussianWeight_nonneg n q x)] using
                abs_add_le (deriv (scaledNumerator tartarNumerator a) x *
                  weilGaussianWeight n q x)
                  (scaledNumerator tartarNumerator a x *
                    deriv (weilGaussianWeight n q) x)
      _ ≤ D₁ * M x + 2 * M x := by
        apply add_le_add
        · exact (mul_le_mul (hb₁ x) hW (weilGaussianWeight_nonneg n q x) hD₁).trans
            (mul_le_mul_of_nonneg_left hbase0 hD₁)
        · calc
            |scaledNumerator tartarNumerator a x| *
                ‖deriv (weilGaussianWeight n q) x‖
                ≤ 1 * (2 * (1 + |x|) *
                  Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)) :=
              mul_le_mul hf0 hW' (norm_nonneg _) (by norm_num)
            _ ≤ 2 * M x := by
              simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbase1 (by norm_num : (0:ℝ) ≤ 2)
      _ = (D₁ + 2) * M x := by ring
  · refine Integrable.mono' (hM.const_mul (D₂ + 4 * D₁ + 7)) (by fun_prop)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [(hasDerivAt_deriv_weilGaussianSymbol a n q x).deriv, Complex.norm_real,
      Real.norm_eq_abs]
    have hf0 : |scaledNumerator tartarNumerator a x| ≤ 1 := by
      unfold scaledNumerator
      rw [abs_of_nonneg (tartarNumerator_nonneg (x / a))]
      exact tartarNumerator_le_one _
    have hW := weilGaussianWeight_le n q x
    have hW' := norm_deriv_weilGaussianWeight_le n hq x
    have hW'' := norm_deriv_deriv_weilGaussianWeight_le n hq x
    have hbase0 := hM0 x
    have hbase1 : (1 + |x|) *
        Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤ M x := by
      dsimp [M]
      have hx : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
      nlinarith [Real.exp_pos (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)]
    calc
      |deriv (deriv (scaledNumerator tartarNumerator a)) x * weilGaussianWeight n q x +
          2 * deriv (scaledNumerator tartarNumerator a) x * deriv (weilGaussianWeight n q) x +
          scaledNumerator tartarNumerator a x * deriv (deriv (weilGaussianWeight n q)) x|
          ≤ ‖deriv (deriv (scaledNumerator tartarNumerator a)) x‖ * weilGaussianWeight n q x +
              2 * ‖deriv (scaledNumerator tartarNumerator a) x‖ *
                ‖deriv (weilGaussianWeight n q) x‖ +
              |scaledNumerator tartarNumerator a x| *
                ‖deriv (deriv (weilGaussianWeight n q)) x‖ := by
            have hab :
                |deriv (deriv (scaledNumerator tartarNumerator a)) x *
                    weilGaussianWeight n q x +
                  2 * deriv (scaledNumerator tartarNumerator a) x *
                    deriv (weilGaussianWeight n q) x| ≤
                  ‖deriv (deriv (scaledNumerator tartarNumerator a)) x‖ *
                    weilGaussianWeight n q x +
                  2 * ‖deriv (scaledNumerator tartarNumerator a) x‖ *
                    ‖deriv (weilGaussianWeight n q) x‖ := by
              calc
                _ ≤ |deriv (deriv (scaledNumerator tartarNumerator a)) x *
                      weilGaussianWeight n q x| +
                    |2 * deriv (scaledNumerator tartarNumerator a) x *
                      deriv (weilGaussianWeight n q) x| := abs_add_le _ _
                _ = _ := by
                  rw [abs_mul, abs_mul, abs_mul, Real.norm_eq_abs,
                    abs_of_nonneg (weilGaussianWeight_nonneg n q x)]
                  norm_num
            exact (abs_add_le _ _).trans (add_le_add hab (by
              rw [abs_mul, Real.norm_eq_abs]))
      _ ≤ D₂ * M x + 4 * D₁ * M x + 7 * M x := by
        apply add_le_add
        · apply add_le_add
          · exact (mul_le_mul (hb₂ x) hW (weilGaussianWeight_nonneg n q x) hD₂).trans
              (mul_le_mul_of_nonneg_left hbase0 hD₂)
          · calc
              2 * ‖deriv (scaledNumerator tartarNumerator a) x‖ *
                    ‖deriv (weilGaussianWeight n q) x‖
                  ≤ 2 * D₁ * (2 * (1 + |x|) *
                    Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)) := by
                    gcongr
                    exact hb₁ x
              _ ≤ 4 * D₁ * M x := by
                nlinarith [mul_le_mul_of_nonneg_left hbase1 hD₁]
        · calc
            |scaledNumerator tartarNumerator a x| *
                ‖deriv (deriv (weilGaussianWeight n q)) x‖
                ≤ 1 * (7 * (1 + |x|) ^ 2 *
                  Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)) :=
              mul_le_mul hf0 hW'' (norm_nonneg _) (by norm_num)
            _ = 7 * M x := by dsimp [M]; ring
      _ = (D₂ + 4 * D₁ + 7) * M x := by ring

/-- At zero tilt, the auxiliary symbol is the Gaussian Poitou approximant. -/
theorem weilGaussianSymbol_zero (a : ℝ) (n : ℕ) :
    weilGaussianSymbol a n 0 =
      gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n := by
  funext x
  rw [weilGaussianSymbol_eq]
  norm_num

private theorem differentiable_weilGaussianSymbol (a : ℝ) (n : ℕ) (q : ℝ) :
    Differentiable ℝ (weilGaussianSymbol a n q) :=
  fun x => (hasDerivAt_weilGaussianSymbol a n q x).differentiableAt

private theorem continuous_weilGaussianSymbol (a : ℝ) (n : ℕ) (q : ℝ) :
    Continuous (weilGaussianSymbol a n q) :=
  (differentiable_weilGaussianSymbol a n q).continuous

private theorem boundedVariationOn_weilGaussianSymbol
    {a : ℝ} (ha : 0 < a) (n : ℕ) {q : ℝ} (hq : |q| ≤ 3 / 4) :
    BoundedVariationOn (weilGaussianSymbol a n q) Set.univ := by
  have hint := (integrable_weilGaussianSymbol_deriv_two ha n hq).2.1
  exact DedekindResidue.boundedVariationOn_of_deriv_integrable
    Set.ordConnected_univ (continuous_weilGaussianSymbol a n q).continuousOn
    (fun x _ => (hasDerivAt_weilGaussianSymbol a n q x).congr_deriv
      (hasDerivAt_weilGaussianSymbol a n q x).deriv.symm)
    hint.integrableOn

private theorem norm_weilGaussianSymbol_zero_le_one (a : ℝ) (n : ℕ) (x : ℝ) :
    ‖weilGaussianSymbol a n 0 x‖ ≤ 1 := by
  rw [weilGaussianSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (weilGaussianWeight_nonneg n 0 x)]
  unfold scaledNumerator
  rw [abs_of_nonneg (tartarNumerator_nonneg (x / a))]
  calc
    tartarNumerator (x / a) * weilGaussianWeight n 0 x
        ≤ weilGaussianWeight n 0 x :=
      mul_le_of_le_one_left (weilGaussianWeight_nonneg n 0 x)
        (tartarNumerator_le_one _)
    _ ≤ Real.exp (-x ^ 2 / ((n : ℝ) + 1)) := by
      simpa using weilGaussianWeight_le n 0 x
    _ ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hc : 0 ≤ (n : ℝ) + 1 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) hc

private theorem integrableOn_weilGaussian_diffQuot
    (a : ℝ) (n : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (weilGaussianSymbol a n 0 0 - weilGaussianSymbol a n 0 x) / (x : ℂ))
      (Set.Ioc (-1) 1) := by
  rw [weilGaussianSymbol_zero]
  exact (continuous_gaussianPoitouApproximant_diffQuot_scaledTartar a n).integrableOn_Icc.mono_set
    Set.Ioc_subset_Icc_self

private theorem memLp_two_weilGaussian_diffQuot (a : ℝ) (n : ℕ) :
    MemLp (fun x : ℝ =>
      (weilGaussianSymbol a n 0 0 - weilGaussianSymbol a n 0 x) / (x : ℂ))
      2 (volume : Measure ℝ) := by
  let Q : ℝ → ℂ := fun x =>
    (weilGaussianSymbol a n 0 0 - weilGaussianSymbol a n 0 x) / (x : ℂ)
  have hQcont : Continuous Q := by
    rw [show Q = fun x : ℝ =>
      (gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n 0 -
        gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n x) / x by
      funext x
      dsimp [Q]
      rw [weilGaussianSymbol_zero]]
    exact continuous_gaussianPoitouApproximant_diffQuot_scaledTartar a n
  rw [memLp_two_iff_integrable_sq_norm hQcont.aestronglyMeasurable]
  have hfar (x : ℝ) (hx : 1 ≤ |x|) : ‖Q x‖ ≤ 2 / |x| := by
    dsimp [Q]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_div_iff_of_pos_right (lt_of_lt_of_le one_pos hx)).2
    exact (norm_sub_le _ _).trans (by
      nlinarith [norm_weilGaussianSymbol_zero_le_one a n 0,
        norm_weilGaussianSymbol_zero_le_one a n x])
  have hraypos : IntegrableOn (fun x : ℝ => ‖Q x‖ ^ 2) (Set.Ioi 1) := by
    refine Integrable.mono' (g := fun x : ℝ => 4 * x ^ (-2 : ℝ))
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 4)
      ((hQcont.norm.pow 2).aestronglyMeasurable.restrict) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [Set.mem_Ioi] at hx
    have hqx := hfar x (by rw [abs_of_pos (one_pos.trans hx)]; exact hx.le)
    rw [abs_of_pos (one_pos.trans hx)] at hqx
    rw [Real.rpow_neg (one_pos.trans hx).le,
      show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖Q x‖ ^ 2 ≤ (2 / x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hqx 2
      _ = 4 * (x ^ 2)⁻¹ := by rw [div_pow]; ring
  have hmiddle : IntegrableOn (fun x : ℝ => ‖Q x‖ ^ 2) (Set.Ioc (-1) 1) :=
    (hQcont.norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hFeven : Function.Even (weilGaussianSymbol a n 0) := by
    rw [weilGaussianSymbol_zero]
    exact poitouKernel_even (gaussianDampedNumerator_even (by
      intro x
      simpa only [scaledNumerator, neg_div] using tartarNumerator_even (x / a)) n)
  have hrayneg : IntegrableOn (fun x : ℝ => ‖Q x‖ ^ 2) (Set.Iic (-1)) := by
    have A : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).restrict (Set.Iic (-1)) =
        Measure.map (fun x : ℝ => -x) ((volume : Measure ℝ).restrict (Set.Ici 1)) := by
      rw [show Set.Ici (1 : ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iic (-1)) by
          ext x
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
          constructor <;> intro h <;> linarith,
        ← Measure.restrict_map A.measurable measurableSet_Iic,
        Measure.map_neg_eq_self (volume : Measure ℝ)]
    rw [IntegrableOn, hmap, A.integrable_map_iff]
    have hIci := hraypos.congr_set_ae (Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
    refine hIci.congr (Filter.Eventually.of_forall (fun x => ?_))
    have hQneg : Q (-x) = -Q x := by
      dsimp [Q]
      rw [hFeven x]
      push_cast
      field_simp
    change ‖Q x‖ ^ 2 = ‖Q (-x)‖ ^ 2
    rw [hQneg, norm_neg]
  have hcover : (Set.univ : Set ℝ) =
      Set.Iic (-1) ∪ (Set.Ioc (-1) 1 ∪ Set.Ioi 1) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioc, Set.mem_Ioi,
      true_iff]
    rcases le_or_gt x (-1) with h | h
    · exact Or.inl h
    · rcases le_or_gt x 1 with h2 | h2
      · exact Or.inr (Or.inl ⟨h, h2⟩)
      · exact Or.inr (Or.inr h2)
  rw [← MeasureTheory.integrableOn_univ, hcover]
  exact hrayneg.union (hmiddle.union hraypos)

private theorem fourier_deriv_scalar_norm (t : ℝ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ))‖ = |t| := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    mul_one, show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
    abs_div, abs_neg, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  field_simp [Real.pi_ne_zero]

private theorem exists_muFT_sq_decay {G : ℝ → ℂ}
    (hG : Integrable G) (hGdiff : Differentiable ℝ G)
    (hG' : Integrable (deriv G)) (hG'diff : Differentiable ℝ (deriv G))
    (hG'' : Integrable (deriv (deriv G))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖∫ x : ℝ, G x * Complex.exp ((t * x : ℝ) * Complex.I)‖ ≤ C / t ^ 2 := by
  let C := ∫ x : ℝ, ‖deriv (deriv G) x‖
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨C, hC, fun t ht => ?_⟩
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hfour : 𝓕 G (-t / (2 * Real.pi)) =
      ∫ x : ℝ, G x * Complex.exp ((t * x : ℝ) * Complex.I) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [smul_eq_mul, mul_comm]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  have hd₁ := congrFun (Real.fourier_deriv hG hGdiff hG') (-t / (2 * Real.pi))
  have hd₂ := congrFun (Real.fourier_deriv hG' hG'diff hG'') (-t / (2 * Real.pi))
  have hn₁ : |t| * ‖𝓕 G (-t / (2 * Real.pi))‖ =
      ‖𝓕 (deriv G) (-t / (2 * Real.pi))‖ := by
    rw [hd₁, norm_smul, fourier_deriv_scalar_norm]
  have hn₂ : |t| * ‖𝓕 (deriv G) (-t / (2 * Real.pi))‖ =
      ‖𝓕 (deriv (deriv G)) (-t / (2 * Real.pi))‖ := by
    rw [hd₂, norm_smul, fourier_deriv_scalar_norm]
  rw [← hfour]
  apply (le_div_iff₀ (sq_pos_of_ne_zero ht0)).2
  calc
    ‖𝓕 G (-t / (2 * Real.pi))‖ * t ^ 2 =
        |t| * (|t| * ‖𝓕 G (-t / (2 * Real.pi))‖) := by
          rw [← sq_abs t]
          ring
    _ = |t| * ‖𝓕 (deriv G) (-t / (2 * Real.pi))‖ := by rw [hn₁]
    _ = ‖𝓕 (deriv (deriv G)) (-t / (2 * Real.pi))‖ := hn₂
    _ ≤ C := VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) (deriv (deriv G)) (-t / (2 * Real.pi))

private theorem integral_halfScale_mul_cexp {F : ℝ → ℂ} (u : ℝ) :
    (∫ x : ℝ, (F (x / 2) / 2) * Complex.exp ((u * x : ℝ) * Complex.I)) =
      ∫ x : ℝ, F x * Complex.exp (((2 * u) * x : ℝ) * Complex.I) := by
  set g : ℝ → ℂ := fun w => F w * Complex.exp (((2 * u) * w : ℝ) * Complex.I)
  have h₁ : (∫ x : ℝ, g ((2 : ℝ)⁻¹ * x)) =
      |(((2 : ℝ)⁻¹))⁻¹| • ∫ x : ℝ, g x :=
    MeasureTheory.Measure.integral_comp_mul_left g ((2 : ℝ)⁻¹)
  have h₂ : (fun x : ℝ => (F (x / 2) / 2) *
      Complex.exp ((u * x : ℝ) * Complex.I)) =
      fun x : ℝ => (1 / 2 : ℂ) * g ((2 : ℝ)⁻¹ * x) := by
    funext x
    dsimp [g]
    rw [show (2 : ℝ)⁻¹ * x = x / 2 by ring,
      show ((2 * u) * (x / 2) : ℝ) = u * x by ring]
    ring
  rw [h₂, MeasureTheory.integral_const_mul, h₁,
    show |(((2 : ℝ)⁻¹))⁻¹| = (2 : ℝ) by norm_num, Complex.real_smul,
    Complex.ofReal_ofNat]
  ring

private theorem tendsto_boundary_weilGaussianSymbol
    {a : ℝ} (ha : 0 < a) (n : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2)
    (l : Filter ℝ) (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ =>
      DedekindResidue.rhoFT (fun x => ((DedekindResidue.poitouKernel σ x : ℝ) : ℂ)) t *
        DedekindResidue.gammaFT (weilGaussianSymbol a n 0) t) l (nhds 0) := by
  obtain ⟨hF, hF', hF''⟩ :=
    integrable_weilGaussianSymbol_deriv_two ha n (q := 0) (by norm_num)
  obtain ⟨C, hC, hφ⟩ := exists_muFT_sq_decay hF
    (differentiable_weilGaussianSymbol a n 0) hF'
    (fun x => (hasDerivAt_deriv_weilGaussianSymbol a n 0 x).differentiableAt) hF''
  refine DedekindResidue.tendsto_rhoFT_mul_gammaFT_of_decay
    (C := C) (γ₀ := 1) hσ hσl hσr ?_ l habs
  exact DedekindResidue.norm_gammaFT_le_of_fourier_decay hF
    (integrableOn_weilGaussian_diffQuot a n) (by norm_num) hφ

private theorem tendsto_boundary_weilGaussianSymbol_half
    {a : ℝ} (ha : 0 < a) (n : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2)
    (l : Filter ℝ) (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ =>
      DedekindResidue.rhoFT (fun x => ((DedekindResidue.poitouKernel σ x : ℝ) : ℂ)) t *
        DedekindResidue.gammaFT
          (fun x : ℝ => weilGaussianSymbol a n 0 (x / 2) / 2) t) l (nhds 0) := by
  obtain ⟨hF, hF', hF''⟩ :=
    integrable_weilGaussianSymbol_deriv_two ha n (q := 0) (by norm_num)
  obtain ⟨C, hC, hφ⟩ := exists_muFT_sq_decay hF
    (differentiable_weilGaussianSymbol a n 0) hF'
    (fun x => (hasDerivAt_deriv_weilGaussianSymbol a n 0 x).differentiableAt) hF''
  refine DedekindResidue.tendsto_rhoFT_mul_gammaFT_of_decay
    (C := C) (γ₀ := 1) hσ hσl hσr ?_ l habs
  have hFh : Integrable (fun x : ℝ => weilGaussianSymbol a n 0 (x / 2) / 2) :=
    DedekindResidue.integrable_halfScale hF
  have hFhdiv : IntegrableOn (fun x : ℝ =>
      ((fun x : ℝ => weilGaussianSymbol a n 0 (x / 2) / 2) 0 -
        (fun x : ℝ => weilGaussianSymbol a n 0 (x / 2) / 2) x) / (x : ℂ))
      (Set.Ioc (-1) 1) := by
    refine (DedekindResidue.integrableOn_halfScale_div
      (integrableOn_weilGaussian_diffQuot a n)).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    norm_num
  refine DedekindResidue.norm_gammaFT_le_of_fourier_decay hFh hFhdiv (by norm_num) ?_
  intro u hu
  rw [integral_halfScale_mul_cexp]
  have h2u : 1 ≤ |2 * u| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [abs_nonneg u]
  refine (hφ (2 * u) h2u).trans ?_
  have hu0 : 0 < u ^ 2 := sq_pos_of_ne_zero (by
    intro h
    rw [h, abs_zero] at hu
    norm_num at hu)
  have hden : u ^ 2 ≤ (2 * u) ^ 2 := by nlinarith [sq_nonneg u]
  exact div_le_div_of_nonneg_left hC hu0 hden

private theorem norm_muFT_le_div_max_of_bounds {G : ℝ → ℂ}
    (hG : Integrable G) (hGdiff : Differentiable ℝ G)
    (hG' : Integrable (deriv G)) {C : ℝ}
    (hC₀ : ∫ x : ℝ, ‖G x‖ ≤ C) (hC₁ : ∫ x : ℝ, ‖deriv G x‖ ≤ C)
    (t : ℝ) :
    ‖∫ x : ℝ, G x * Complex.exp ((t * x : ℝ) * Complex.I)‖ ≤
      C / max |t| 1 := by
  have hfour : 𝓕 G (-t / (2 * Real.pi)) =
      ∫ x : ℝ, G x * Complex.exp ((t * x : ℝ) * Complex.I) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [smul_eq_mul, mul_comm]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← hfour]
  by_cases ht : |t| ≤ 1
  · rw [max_eq_right ht, div_one]
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm
      𝐞 volume (innerₗ ℝ) G (-t / (2 * Real.pi))).trans hC₀
  · have ht1 : 1 < |t| := lt_of_not_ge ht
    rw [max_eq_left ht1.le]
    have hd := congrFun (Real.fourier_deriv hG hGdiff hG') (-t / (2 * Real.pi))
    have hn : |t| * ‖𝓕 G (-t / (2 * Real.pi))‖ =
        ‖𝓕 (deriv G) (-t / (2 * Real.pi))‖ := by
      rw [hd, norm_smul, fourier_deriv_scalar_norm]
    apply (le_div_iff₀ (one_pos.trans ht1)).2
    calc
      ‖𝓕 G (-t / (2 * Real.pi))‖ * |t| =
          |t| * ‖𝓕 G (-t / (2 * Real.pi))‖ := mul_comm _ _
      _ = ‖𝓕 (deriv G) (-t / (2 * Real.pi))‖ := hn
      _ ≤ ∫ x : ℝ, ‖deriv G x‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm
          𝐞 volume (innerₗ ℝ) (deriv G) (-t / (2 * Real.pi))
      _ ≤ C := hC₁

private theorem exists_uniform_muFT_weilGaussianSymbol
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q t : ℝ, |q| ≤ 3 / 4 →
      ‖∫ x : ℝ, weilGaussianSymbol a n q x *
        Complex.exp ((t * x : ℝ) * Complex.I)‖ ≤ C / max |t| 1 := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hb₁, hb₂⟩ :=
    exists_bounds_deriv_scaledTartarNumerator ha
  let M : ℝ → ℝ := fun x => (1 + |x|) ^ 2 *
    Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * |x|)
  have hM : Integrable M := by
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)] using
      integrable_weilGaussian_majorant n (3 / 4)
  let A := ∫ x : ℝ, M x
  let C := max A ((D₁ + 2) * A)
  have hM0 : 0 ≤ M := fun x => by dsimp [M]; positivity
  have hA : 0 ≤ A := integral_nonneg hM0
  have hC : 0 ≤ C := le_trans hA (le_max_left _ _)
  refine ⟨C, hC, fun q t hq => ?_⟩
  obtain ⟨hG, hG', hG''⟩ := integrable_weilGaussianSymbol_deriv_two ha n hq
  have hbase (x : ℝ) :
      Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤ M x := by
    dsimp [M]
    have hexp : Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤
        Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * |x|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg x]
    have hpoly : 1 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
    exact hexp.trans ((le_mul_iff_one_le_left (Real.exp_pos _)).2 hpoly)
  have hnorm (x : ℝ) : ‖weilGaussianSymbol a n q x‖ ≤ M x := by
    rw [weilGaussianSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (weilGaussianWeight_nonneg n q x)]
    unfold scaledNumerator
    rw [abs_of_nonneg (tartarNumerator_nonneg (x / a))]
    exact (mul_le_of_le_one_left (weilGaussianWeight_nonneg n q x)
      (tartarNumerator_le_one _)).trans ((weilGaussianWeight_le n q x).trans (hbase x))
  have hnorm' (x : ℝ) : ‖deriv (weilGaussianSymbol a n q) x‖ ≤
      (D₁ + 2) * M x := by
    rw [(hasDerivAt_weilGaussianSymbol a n q x).deriv, Complex.norm_real,
      Real.norm_eq_abs]
    have hf0 : |scaledNumerator tartarNumerator a x| ≤ 1 := by
      unfold scaledNumerator
      rw [abs_of_nonneg (tartarNumerator_nonneg (x / a))]
      exact tartarNumerator_le_one _
    have hbase1 : (1 + |x|) *
        Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤ M x := by
      dsimp [M]
      have hexp : Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤
          Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * |x|) := by
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg x]
      have hx : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
      calc
        (1 + |x|) * Real.exp
            (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|) ≤
            (1 + |x|) * Real.exp
              (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * |x|) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ (1 + |x|) ^ 2 * Real.exp
              (-x ^ 2 / ((n : ℝ) + 1) + (3 / 4) * |x|) := by
          gcongr
          nlinarith [abs_nonneg x]
    calc
      |deriv (scaledNumerator tartarNumerator a) x * weilGaussianWeight n q x +
          scaledNumerator tartarNumerator a x * deriv (weilGaussianWeight n q) x|
          ≤ ‖deriv (scaledNumerator tartarNumerator a) x‖ * weilGaussianWeight n q x +
              |scaledNumerator tartarNumerator a x| *
                ‖deriv (weilGaussianWeight n q) x‖ := by
            simpa [abs_mul, Real.norm_eq_abs,
              abs_of_nonneg (weilGaussianWeight_nonneg n q x)] using
                abs_add_le (deriv (scaledNumerator tartarNumerator a) x *
                  weilGaussianWeight n q x)
                  (scaledNumerator tartarNumerator a x * deriv (weilGaussianWeight n q) x)
      _ ≤ D₁ * M x + 2 * M x := by
        apply add_le_add
        · exact (mul_le_mul (hb₁ x) (weilGaussianWeight_le n q x)
            (weilGaussianWeight_nonneg n q x) hD₁).trans
              (mul_le_mul_of_nonneg_left (hbase x) hD₁)
        · calc
            |scaledNumerator tartarNumerator a x| *
                ‖deriv (weilGaussianWeight n q) x‖ ≤
                1 * (2 * (1 + |x|) *
                  Real.exp (-x ^ 2 / ((n : ℝ) + 1) + |q| * |x|)) :=
              mul_le_mul hf0 (norm_deriv_weilGaussianWeight_le n hq x)
                (norm_nonneg _) (by norm_num)
            _ ≤ 2 * M x := by
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hbase1 (by norm_num : (0 : ℝ) ≤ 2)
      _ = (D₁ + 2) * M x := by ring
  have hI₀ : ∫ x : ℝ, ‖weilGaussianSymbol a n q x‖ ≤ C :=
    (integral_mono hG.norm hM hnorm).trans (le_max_left _ _)
  have hDM : Integrable (fun x => (D₁ + 2) * M x) := hM.const_mul _
  have hI₁ : ∫ x : ℝ, ‖deriv (weilGaussianSymbol a n q) x‖ ≤ C :=
    (integral_mono hG'.norm hDM hnorm').trans (by
      rw [integral_const_mul]
      exact le_max_right _ _)
  exact norm_muFT_le_div_max_of_bounds hG
    (differentiable_weilGaussianSymbol a n q) hG' hI₀ hI₁ t

private theorem paperPhi_weilGaussianSymbol_eq_muFT
    (a : ℝ) (n : ℕ) (σ t : ℝ) :
    DedekindResidue.paperPhi (weilGaussianSymbol a n 0)
        ((σ : ℂ) + (t : ℂ) * Complex.I) =
      ∫ x : ℝ, weilGaussianSymbol a n (σ - 1 / 2) x *
        Complex.exp ((t * x : ℝ) * Complex.I) := by
  rw [DedekindResidue.paperPhi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [weilGaussianSymbol_eq, weilGaussianSymbol_eq]
  simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem exists_band_bound_paperPhi_weilGaussianSymbol
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, -(1 / 8 : ℝ) ≤ σ → σ ≤ 1 + 1 / 8 →
      ‖DedekindResidue.paperPhi (weilGaussianSymbol a n 0)
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / max |t| 1 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_muFT_weilGaussianSymbol ha n
  refine ⟨C, hC, fun σ t hσ₁ hσ₂ => ?_⟩
  rw [paperPhi_weilGaussianSymbol_eq_muFT]
  exact hb (σ - 1 / 2) t (by
    rw [abs_le]
    constructor <;> linarith)

private theorem norm_weilGaussianSymbol_band_le
    (a : ℝ) (n : ℕ) (x : ℝ) :
    ‖weilGaussianSymbol a n (5 / 8) x‖ ≤
      Real.exp (((n : ℝ) + 1) * (5 / 8) ^ 2 / 4) := by
  rw [weilGaussianSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (weilGaussianWeight_nonneg n (5 / 8) x)]
  unfold scaledNumerator
  rw [abs_of_nonneg (tartarNumerator_nonneg (x / a))]
  calc
    tartarNumerator (x / a) * weilGaussianWeight n (5 / 8) x
        ≤ weilGaussianWeight n (5 / 8) x :=
      mul_le_of_le_one_left (weilGaussianWeight_nonneg n (5 / 8) x)
        (tartarNumerator_le_one _)
    _ ≤ Real.exp (-x ^ 2 / ((n : ℝ) + 1) + (5 / 8) * |x|) := by
      simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8)] using
        weilGaussianWeight_le n (5 / 8) x
    _ ≤ Real.exp (((n : ℝ) + 1) * (5 / 8) ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      have hd : 0 < (n : ℝ) + 1 := by positivity
      rw [show -x ^ 2 / ((n : ℝ) + 1) + (5 / 8) * |x| =
        (-x ^ 2 + (5 / 8) * |x| * ((n : ℝ) + 1)) /
          ((n : ℝ) + 1) by field_simp]
      apply (div_le_iff₀ hd).2
      nlinarith [sq_nonneg (|x| - ((n : ℝ) + 1) * (5 / 8) / 2), sq_abs x]

private theorem summable_primeSideH_term_weilGaussianSymbol
    (K : Type*) [Field K] [NumberField K]
    (a : ℝ) (n : ℕ) (u : ℝ) :
    Summable (fun pk :
        {𝔭 : Ideal (NumberField.RingOfIntegers K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      ((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^
            (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + 1 / 8)) : ℝ) : ℂ) *
        weilGaussianSymbol a n (5 / 8)
          (u + (((pk.2 + 1 : ℕ)) : ℝ) *
            Real.log (Ideal.absNorm pk.1.1))) := by
  let C := Real.exp (((n : ℝ) + 1) * (5 / 8) ^ 2 / 4)
  refine Summable.of_norm_bounded
    (g := fun pk :
      {𝔭 : Ideal (NumberField.RingOfIntegers K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^
          (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + 1 / 8)) * C)
    ((DedekindResidue.summable_primeIdeal_pow_log_rpow K
      (by norm_num : (1 : ℝ) < 1 + 1 / 8)).mul_right C) (fun pk => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (DedekindResidue.primeSideH_weight_nonneg
      (K := K) (a := (1 / 8 : ℝ)) pk)]
  exact mul_le_mul_of_nonneg_left
    (norm_weilGaussianSymbol_band_le a n _)
    (DedekindResidue.primeSideH_weight_nonneg
      (K := K) (a := (1 / 8 : ℝ)) pk)

private theorem primeSideH_weilGaussianSymbol_eq
    (K : Type*) [Field K] [NumberField K]
    (a : ℝ) (n : ℕ) (u : ℝ) :
    DedekindResidue.primeSideH K (1 / 8)
        (weilGaussianSymbol a n 0) u =
      ∑' pk :
          {𝔭 : Ideal (NumberField.RingOfIntegers K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
        ((Real.log (Ideal.absNorm pk.1.1)
            * (Ideal.absNorm pk.1.1 : ℝ) ^
              (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + 1 / 8)) : ℝ) : ℂ) *
          weilGaussianSymbol a n (5 / 8)
            (u + (((pk.2 + 1 : ℕ)) : ℝ) *
              Real.log (Ideal.absNorm pk.1.1)) := by
  rw [DedekindResidue.primeSideH]
  apply tsum_congr
  intro pk
  congr 1
  rw [weilGaussianSymbol_eq, weilGaussianSymbol_eq]
  norm_num

private theorem boundedVariationOn_primeSideH_weilGaussianSymbol
    (K : Type*) [Field K] [NumberField K]
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    BoundedVariationOn
      (DedekindResidue.primeSideH K (1 / 8)
        (weilGaussianSymbol a n 0)) Set.univ := by
  let G := weilGaussianSymbol a n (5 / 8)
  have hGbv : BoundedVariationOn G Set.univ :=
    boundedVariationOn_weilGaussianSymbol ha n (by norm_num)
  have h0 : DedekindResidue.primeSideH K (1 / 8)
      (weilGaussianSymbol a n 0) = fun u : ℝ =>
        ∑' pk :
            {𝔭 : Ideal (NumberField.RingOfIntegers K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
          ((Real.log (Ideal.absNorm pk.1.1)
              * (Ideal.absNorm pk.1.1 : ℝ) ^
                (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + 1 / 8)) : ℝ) : ℂ) *
            G (u + (((pk.2 + 1 : ℕ)) : ℝ) *
              Real.log (Ideal.absNorm pk.1.1)) := by
    funext u
    exact primeSideH_weilGaussianSymbol_eq K a n u
  have hwsum : Summable (fun pk :
      {𝔭 : Ideal (NumberField.RingOfIntegers K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^
          (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + 1 / 8))) :=
    DedekindResidue.summable_primeIdeal_pow_log_rpow K
      (by norm_num : (1 : ℝ) < 1 + 1 / 8)
  have hwsum' : Summable (fun pk :
      {𝔭 : Ideal (NumberField.RingOfIntegers K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      ‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^
            (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + 1 / 8)) : ℝ) : ℂ)‖₊) := by
    rw [← NNReal.summable_coe]
    refine hwsum.congr (fun pk => ?_)
    rw [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (DedekindResidue.primeSideH_weight_nonneg
        (K := K) (a := (1 / 8 : ℝ)) pk)]
  have hwtop : (∑' pk :
      {𝔭 : Ideal (NumberField.RingOfIntegers K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
      (‖((Real.log (Ideal.absNorm pk.1.1)
          * (Ideal.absNorm pk.1.1 : ℝ) ^
            (-(((pk.2 + 1 : ℕ)) : ℝ) * (1 + 1 / 8)) : ℝ) : ℂ)‖₊ : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hwsum'
  unfold BoundedVariationOn
  rw [h0]
  refine ne_top_of_le_ne_top ?_
    (DedekindResidue.eVariationOn_tsum_le _ _ (fun u _ => by
      dsimp [G]
      exact summable_primeSideH_term_weilGaussianSymbol K a n u))
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (fun pk =>
    DedekindResidue.eVariationOn_smul_translate_le G _ _))
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top hwtop hGbv

private theorem continuous_primeSideH_weilGaussianSymbol
    (K : Type*) [Field K] [NumberField K]
    (a : ℝ) (n : ℕ) :
    Continuous (DedekindResidue.primeSideH K (1 / 8)
      (weilGaussianSymbol a n 0)) := by
  rw [funext (primeSideH_weilGaussianSymbol_eq K a n)]
  let C := Real.exp (((n : ℝ) + 1) * (5 / 8) ^ 2 / 4)
  refine continuous_tsum (fun pk => ?_)
    ((DedekindResidue.summable_primeIdeal_pow_log_rpow K
      (by norm_num : (1 : ℝ) < 1 + 1 / 8)).mul_right C) (fun pk u => ?_)
  · exact continuous_const.mul
      ((continuous_weilGaussianSymbol a n (5 / 8)).comp
        (continuous_id.add continuous_const))
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (DedekindResidue.primeSideH_weight_nonneg
        (K := K) (a := (1 / 8 : ℝ)) pk)]
    exact mul_le_mul_of_nonneg_left
      (norm_weilGaussianSymbol_band_le a n _)
      (DedekindResidue.primeSideH_weight_nonneg
        (K := K) (a := (1 / 8 : ℝ)) pk)

/-- The generic Weil formula supplies a convergent zero-window sequence for every
Gaussian Tartar approximant, with the fixed band width `1/8`. -/
theorem gaussianTartarWeilWindowLimit
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      Tendsto (fun m : ℕ => ∑ᶠ z,
        ((MeromorphicOn.divisor
          (DedekindResidue.completedDedekindZetaEntire K)
          (Set.Ioo (-(1 / 8 : ℝ)) (1 + 1 / 8) ×ℂ
            Set.Ioo (-(T m)) (T m))) z : ℂ) *
          DedekindResidue.paperPhi (weilGaussianSymbol a n 0) z)
        atTop (nhds (totallyComplexZeroSide K
          (weilGaussianSymbol a n 0)
          (DedekindResidue.paperPhi (weilGaussianSymbol a n 0))
          (poitouArchimedeanIntegral (weilGaussianSymbol a n 0))
          (DedekindResidue.primeSideH K (1 / 8)
            (weilGaussianSymbol a n 0) 0))) := by
  let F := weilGaussianSymbol a n 0
  have hAdm : DedekindResidue.IsAdmissibleTestFn F := by
    simpa only [F, weilGaussianSymbol_zero] using
      gaussianPoitouApproximant_isAdmissible_scaledTartar ha.ne' n
  obtain ⟨hF, _, _⟩ :=
    integrable_weilGaussianSymbol_deriv_two ha n (q := 0) (by norm_num)
  have hFbv : BoundedVariationOn F Set.univ :=
    boundedVariationOn_weilGaussianSymbol ha n (q := 0) (by norm_num)
  have hre : LocallyBoundedVariationOn (fun x : ℝ => (F x).re) Set.univ :=
    ((DedekindResidue.lipschitzWith_complex_re).comp_boundedVariationOn
      hFbv).locallyBoundedVariationOn
  have him : LocallyBoundedVariationOn (fun x : ℝ => (F x).im) Set.univ :=
    ((DedekindResidue.lipschitzWith_complex_im).comp_boundedVariationOn
      hFbv).locallyBoundedVariationOn
  have hF0 : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)) :=
    ((continuous_weilGaussianSymbol a n 0).continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x) / (x : ℂ))
      (Set.Ioc (-1) 1) := integrableOn_weilGaussian_diffQuot a n
  have hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x) / (x : ℂ)) 2
      (volume : Measure ℝ) := memLp_two_weilGaussian_diffQuot a n
  obtain ⟨C, hC, hband⟩ := exists_band_bound_paperPhi_weilGaussianSymbol ha n
  have hint : IntegrableOn (fun x : ℝ =>
      F x * ((Real.exp ((1 / 2 + 1 / 4) * x) : ℝ) : ℂ)) (Set.Ici 0) := by
    have hfull := (integrable_weilGaussianSymbol_deriv_two ha n
      (q := 3 / 4) (by norm_num)).1
    have heq : (fun x : ℝ =>
        F x * ((Real.exp ((1 / 2 + 1 / 4) * x) : ℝ) : ℂ)) =
        weilGaussianSymbol a n (3 / 4) := by
      funext x
      dsimp [F]
      rw [weilGaussianSymbol_eq, weilGaussianSymbol_eq]
      norm_num
    rw [heq]
    exact hfull.integrableOn
  have hΦd : ∀ ζ : ℂ, -(1 / 8 : ℝ) ≤ ζ.re → ζ.re ≤ 1 + 1 / 8 →
      DifferentiableAt ℂ (DedekindResidue.paperPhi F) ζ := by
    intro ζ hζ₁ hζ₂
    exact (DedekindResidue.hasDerivAt_paperPhi hAdm
      (ε := (1 / 4 : ℝ)) (by norm_num) hint
      (by linarith) (by linarith)).differentiableAt
  have hG : Integrable (fun x : ℝ =>
      F x * ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ)) := by
    have hfull := (integrable_weilGaussianSymbol_deriv_two ha n
      (q := 5 / 8) (by norm_num)).1
    have heq : (fun x : ℝ =>
        F x * ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ)) =
        weilGaussianSymbol a n (5 / 8) := by
      funext x
      dsimp [F]
      rw [weilGaussianSymbol_eq, weilGaussianSymbol_eq]
      norm_num
    rwa [heq]
  have hGc : Continuous (fun x : ℝ =>
      F x * ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ)) := by
    exact (continuous_weilGaussianSymbol a n 0).mul
      (Complex.continuous_ofReal.comp (by fun_prop))
  have hGbv : BoundedVariationOn (fun x : ℝ =>
      F x * ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ)) Set.univ := by
    have heq : (fun x : ℝ =>
        F x * ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ)) =
        weilGaussianSymbol a n (5 / 8) := by
      funext x
      dsimp [F]
      rw [weilGaussianSymbol_eq, weilGaussianSymbol_eq]
      norm_num
    rw [heq]
    exact boundedVariationOn_weilGaussianSymbol ha n (by norm_num)
  have hGre : LocallyBoundedVariationOn (fun x : ℝ =>
      ((F x * ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ))).re) Set.univ :=
    ((DedekindResidue.lipschitzWith_complex_re).comp_boundedVariationOn
      hGbv).locallyBoundedVariationOn
  have hGim : LocallyBoundedVariationOn (fun x : ℝ =>
      ((F x * ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ))).im) Set.univ :=
    ((DedekindResidue.lipschitzWith_complex_im).comp_boundedVariationOn
      hGbv).locallyBoundedVariationOn
  have hE := DedekindResidue.locallyBoundedVariationOn_poleWindow_add
    (G := fun x : ℝ => F x *
      ((Real.exp ((1 / 2 + 1 / 8) * x) : ℝ) : ℂ))
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (0 : ℝ) < 1 + 1 / 8) hG hGc
  have hEre := (DedekindResidue.lipschitzWith_complex_re).comp_locallyBoundedVariationOn hE
  have hEim := (DedekindResidue.lipschitzWith_complex_im).comp_locallyBoundedVariationOn hE
  have hHbv := boundedVariationOn_primeSideH_weilGaussianSymbol K ha n
  have hHre :=
    ((DedekindResidue.lipschitzWith_complex_re).comp_boundedVariationOn
      hHbv).locallyBoundedVariationOn
  have hHim :=
    ((DedekindResidue.lipschitzWith_complex_im).comp_boundedVariationOn
      hHbv).locallyBoundedVariationOn
  have hHc := continuous_primeSideH_weilGaussianSymbol K a n
  have hHp : Tendsto (DedekindResidue.primeSideH K (1 / 8) F)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (DedekindResidue.primeSideH K (1 / 8) F 0)) :=
    hHc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hHm : Tendsto (DedekindResidue.primeSideH K (1 / 8) F)
      (nhdsWithin 0 (Set.Iio 0))
      (nhds (DedekindResidue.primeSideH K (1 / 8) F 0)) :=
    hHc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨T, hT, hlim⟩ := DedekindResidue.weil_explicit_formula K
    (F := F) (a := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
    hF hre him hF0 hAdm.even hFdiv hFdiv2
    (tendsto_boundary_weilGaussianSymbol ha n (by norm_num) (by norm_num)
      (by norm_num) atTop tendsto_abs_atTop_atTop)
    (tendsto_boundary_weilGaussianSymbol ha n (by norm_num) (by norm_num)
      (by norm_num) atBot tendsto_abs_atBot_atTop)
    (tendsto_boundary_weilGaussianSymbol_half ha n (by norm_num) (by norm_num)
      (by norm_num) atTop tendsto_abs_atTop_atTop)
    (tendsto_boundary_weilGaussianSymbol_half ha n (by norm_num) (by norm_num)
      (by norm_num) atBot tendsto_abs_atBot_atTop)
    hΦd (B := fun t : ℝ => C / max t 1)
    (fun σ t hσ₁ hσ₂ => hband σ t hσ₁ hσ₂)
    (DedekindResidue.tendsto_div_max_mul_log_sq C)
    hG hGre hGim hEre hEim hHre hHim hHp hHm
  refine ⟨T, hT, ?_⟩
  rw [weilLimit_eq_totallyComplexZeroSide K F
    (DedekindResidue.primeSideH K (1 / 8) F 0)] at hlim
  exact hlim

/-- The scaled Gaussian Tartar approximant satisfies the totally complex explicit
formula, and its zero side is nonnegative, without any analytic side hypothesis. -/
theorem gaussianTartarExplicitFormula
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    TotallyComplexExplicitFormula K
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n)
        (DedekindResidue.paperPhi
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (totallyComplexZeroSide K
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n)
          (DedekindResidue.paperPhi
            (gaussianPoitouApproximant
              (scaledNumerator tartarNumerator (1 / √y)) n))
          (poitouArchimedeanIntegral
            (gaussianPoitouApproximant
              (scaledNumerator tartarNumerator (1 / √y)) n))
          (DedekindResidue.primeSideH K (1 / 8)
            (gaussianPoitouApproximant
              (scaledNumerator tartarNumerator (1 / √y)) n) 0))
        (poitouArchimedeanIntegral
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (DedekindResidue.primeSideH K (1 / 8)
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n) 0)
      ∧ 0 ≤ (totallyComplexZeroSide K
        (gaussianPoitouApproximant
          (scaledNumerator tartarNumerator (1 / √y)) n)
        (DedekindResidue.paperPhi
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (poitouArchimedeanIntegral
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n))
        (DedekindResidue.primeSideH K (1 / 8)
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n) 0)).re := by
  have hscale : 0 < 1 / √y := by positivity
  obtain ⟨T, _, hlim⟩ := gaussianTartarWeilWindowLimit K hscale n
  apply gaussianTartarExplicitFormula_of_window_limit K hy n
    (a := (1 / 8 : ℝ)) (T := T)
  simpa only [weilGaussianSymbol_zero] using hlim

end Odlyzko
