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
open scoped FourierTransform Topology ContDiff

namespace Odlyzko

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

end Odlyzko
