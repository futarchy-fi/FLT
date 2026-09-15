/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.TartarSmoothness

/-!
# Bounded variation for the Tartar test function

The normalized Tartar numerator has an integrable derivative by Plancherel and Hölder.
Taylor bounds at zero and elementary hyperbolic estimates then discharge both bounded-variation
conditions in Poitou's weak unconditional test class.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace Odlyzko

private noncomputable def tartarFourierDerivSource (x : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • complexify tartarV x

private theorem continuous_tartarFourierDerivSource :
    Continuous tartarFourierDerivSource := by
  unfold tartarFourierDerivSource complexify
  exact ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal).smul
    (Complex.continuous_ofReal.comp continuous_tartarV)

private theorem hasCompactSupport_tartarFourierDerivSource :
    HasCompactSupport tartarFourierDerivSource := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  simp only [tartarFourierDerivSource, complexify]
  rw [tartarV_eq_zero_of_one_le_abs]
  · simp
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      exact hx.le

private theorem integrable_tartarFourierDerivSource :
    Integrable tartarFourierDerivSource :=
  continuous_tartarFourierDerivSource.integrable_of_hasCompactSupport
    hasCompactSupport_tartarFourierDerivSource

private theorem memLp_tartarFourierDerivSource :
    MemLp tartarFourierDerivSource 2 (volume : Measure ℝ) :=
  continuous_tartarFourierDerivSource.memLp_of_hasCompactSupport
    hasCompactSupport_tartarFourierDerivSource

private theorem memLp_fourier_tartarFourierDerivSource :
    MemLp (𝓕 tartarFourierDerivSource) 2 (volume : Measure ℝ) := by
  exact (MeasureTheory.Lp.memLp _).ae_eq
    (DedekindResidue.coeFn_fourier_toLp_two integrable_tartarFourierDerivSource
      memLp_tartarFourierDerivSource)

private theorem integrable_id_smul_complexify_tartarV :
    Integrable (fun x : ℝ => x • complexify tartarV x) := by
  have hcont : Continuous (fun x : ℝ => x • complexify tartarV x) := by
    simp only [complexify]
    exact Complex.continuous_ofReal.mul
      (Complex.continuous_ofReal.comp continuous_tartarV)
  have hsupp : HasCompactSupport (fun x : ℝ => x • complexify tartarV x) := by
    refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
    intro y hy
    simp only [complexify]
    rw [tartarV_eq_zero_of_one_le_abs]
    · simp
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        exact hy.le
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem memLp_deriv_fourier_tartarV :
    MemLp (deriv (𝓕 (complexify tartarV))) 2 (volume : Measure ℝ) := by
  change MemLp (deriv (𝓕 (fun a : ℝ => Complex.ofRealCLM (tartarV a)))) 2
    (volume : Measure ℝ)
  rw [Real.deriv_fourier
    (Complex.ofRealCLM.integrable_comp integrable_tartarV)
    integrable_id_smul_complexify_tartarV]
  have hsource :
      (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) •
        Complex.ofRealCLM (tartarV x)) = tartarFourierDerivSource := by
    rfl
  rw [hsource]
  exact memLp_fourier_tartarFourierDerivSource

private theorem contDiff_fourier_tartarV :
    ContDiff ℝ ∞ (𝓕 (complexify tartarV)) := by
  apply Real.contDiff_fourier (N := ⊤)
  intro n _
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow n).mul
      (Complex.continuous_ofReal.comp continuous_tartarV).norm
  · refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have habs : 1 ≤ |x| := by
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        exact hx.le
    unfold complexify
    rw [tartarV_eq_zero_of_one_le_abs habs]
    simp

theorem fourier_tartarV_im_eq_zero (x : ℝ) :
    (𝓕 (complexify tartarV) x).im = 0 := by
  have h := congrArg Complex.im (fourier_tartarV_conj x)
  simp only [Complex.conj_im] at h
  linarith

theorem tartarNumerator_eq_re_sq (x : ℝ) :
    tartarNumerator x = 9 / 16 * (𝓕 (complexify tartarV) (x / (2 * Real.pi))).re ^ 2 := by
  rw [tartarNumerator_eq_norm_sq, Complex.sq_norm, Complex.normSq_apply,
    fourier_tartarV_im_eq_zero]
  ring

private theorem hasDerivAt_fourier_tartarV_re (x : ℝ) :
    HasDerivAt (fun u : ℝ => (𝓕 (complexify tartarV) u).re)
      (deriv (𝓕 (complexify tartarV)) x).re x := by
  have hdiff : DifferentiableAt ℝ (𝓕 (complexify tartarV)) x :=
    contDiff_fourier_tartarV.differentiable (by simp) x
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hdiff.hasDerivAt

theorem hasDerivAt_tartarNumerator (x : ℝ) :
    HasDerivAt tartarNumerator
      (9 / (8 * (2 * Real.pi)) *
        ((𝓕 (complexify tartarV) (x / (2 * Real.pi))).re *
          (deriv (𝓕 (complexify tartarV)) (x / (2 * Real.pi))).re)) x := by
  rw [show tartarNumerator = fun u : ℝ =>
      9 / 16 * (𝓕 (complexify tartarV) (u / (2 * Real.pi))).re ^ 2 by
    funext u
    exact tartarNumerator_eq_re_sq u]
  have hinner := (hasDerivAt_fourier_tartarV_re (x / (2 * Real.pi))).comp x
    ((hasDerivAt_id x).div_const (2 * Real.pi))
  change HasDerivAt
    (fun u : ℝ => (𝓕 (complexify tartarV) (u / (2 * Real.pi))).re)
    ((deriv (𝓕 (complexify tartarV)) (x / (2 * Real.pi))).re *
      (1 / (2 * Real.pi))) x at hinner
  have hinner' : HasDerivAt
      (fun u : ℝ => (𝓕 (complexify tartarV) (u / (2 * Real.pi))).re)
      ((deriv (𝓕 (complexify tartarV)) (x / (2 * Real.pi))).re *
        (1 / (2 * Real.pi))) x := by
    exact hinner
  refine ((hinner'.pow 2).const_mul (9 / 16)).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [Real.pi_ne_zero]
  ring

theorem integrable_deriv_tartarNumerator : Integrable (deriv tartarNumerator) := by
  have hprod : Integrable (fun x : ℝ =>
      (𝓕 (complexify tartarV) x).re *
        (deriv (𝓕 (complexify tartarV)) x).re) :=
    memLp_fourier_tartarV.re.integrable_mul memLp_deriv_fourier_tartarV.re
  have hscaled := (integrable_comp_div_iff _
    (by positivity : (2 * Real.pi : ℝ) ≠ 0)).2 hprod
  have hformula : deriv tartarNumerator = fun x : ℝ =>
      9 / (8 * (2 * Real.pi)) *
        ((𝓕 (complexify tartarV) (x / (2 * Real.pi))).re *
          (deriv (𝓕 (complexify tartarV)) (x / (2 * Real.pi))).re) := by
    funext x
    exact (hasDerivAt_tartarNumerator x).deriv
  rw [hformula]
  exact hscaled.const_mul _

theorem integrable_deriv_scaledTartarNumerator {a : ℝ} (ha : a ≠ 0) :
    Integrable (deriv (scaledNumerator tartarNumerator a)) := by
  have hformula : deriv (scaledNumerator tartarNumerator a) =
      fun x : ℝ => deriv tartarNumerator (x / a) / a := by
    funext x
    have hbase : HasDerivAt tartarNumerator (deriv tartarNumerator (x / a)) (x / a) :=
      ((contDiff_tartarNumerator.differentiable (by simp)) (x / a)).hasDerivAt
    have h := hbase.comp x ((hasDerivAt_id x).div_const a)
    change HasDerivAt (fun u : ℝ => tartarNumerator (u / a))
      (deriv tartarNumerator (x / a) * (1 / a)) x at h
    change deriv (fun u : ℝ => tartarNumerator (u / a)) x = _
    rw [h.deriv]
    ring
  rw [hformula]
  exact ((integrable_comp_div_iff _ ha).2 integrable_deriv_tartarNumerator).div_const _

private theorem exists_quadratic_bound_of_contDiff_two
    {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hF' : deriv F 0 = 0) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖F x - F 0‖ ≤ C * x ^ 2 := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := F) (a := (0 : ℝ)) (b := 1) (n := 1) zero_le_one hF.contDiffOn
  refine ⟨C, fun x hx => ?_⟩
  have hu : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) 0 :=
    (uniqueDiffOn_Icc zero_lt_one) 0 (by simp)
  have hdw : derivWithin F (Set.Icc (0 : ℝ) 1) 0 = deriv F 0 :=
    (hF.differentiable (by norm_num) 0).derivWithin hu
  have htaylor : taylorWithinEval F 1 (Set.Icc (0 : ℝ) 1) 0 x = F 0 := by
    rw [show 1 = 0 + 1 by norm_num, taylorWithinEval_succ, taylor_within_zero_eval]
    simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one, one_mul, inv_one,
      sub_zero, pow_one, iteratedDerivWithin_one, hdw, hF', smul_zero, add_zero]
  have hxbound := hC x hx
  rw [htaylor] at hxbound
  norm_num [pow_two] at hxbound ⊢
  exact hxbound

private theorem exists_linear_bound_deriv_of_contDiff_two
    {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hF' : deriv F 0 = 0) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖deriv F x‖ ≤ C * x := by
  have hd : ContDiff ℝ 1 (deriv F) := hF.deriv'
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := deriv F) (a := (0 : ℝ)) (b := 1) (n := 0) zero_le_one hd.contDiffOn
  refine ⟨C, fun x hx => ?_⟩
  have hxbound := hC x hx
  norm_num [hF'] at hxbound ⊢
  exact hxbound

private noncomputable def smoothDiffQuot (F : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (F 0 - F x) / x

private noncomputable def smoothDiffQuotDeriv (F : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (F x - F 0 - (x : ℂ) * deriv F x) / (x : ℂ) ^ 2

private theorem continuous_smoothDiffQuot {F : ℝ → ℂ}
    (hF : Differentiable ℝ F) (hF' : deriv F 0 = 0) :
    Continuous (smoothDiffQuot F) := by
  have hdslope : Continuous (dslope F 0) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact continuousAt_dslope_same.2 (hF 0)
    · exact (continuousAt_dslope_of_ne hx).2 hF.continuous.continuousAt
  have heq : smoothDiffQuot F = fun x => -dslope F 0 x := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [smoothDiffQuot, dslope_same, hF']
    · rw [smoothDiffQuot, dslope_of_ne _ hx, slope_def_module]
      have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      simp only [sub_zero, Algebra.smul_def]
      push_cast
      field_simp [hxc]
      rw [← mul_neg, neg_sub]
      exact mul_comm _ _
  rw [heq]
  exact hdslope.neg

private theorem hasDerivAt_smoothDiffQuot {F : ℝ → ℂ}
    (hF : Differentiable ℝ F) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (smoothDiffQuot F) (smoothDiffQuotDeriv F x) x := by
  have hnum := (hasDerivAt_const x (F 0)).sub (hF x).hasDerivAt
  have hden : HasDerivAt (fun u : ℝ => ((u : ℝ) : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have h := hnum.div hden hxc
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl)) |>.congr_deriv ?_
  simp only [smoothDiffQuotDeriv]
  field_simp [hxc]
  simp only [Pi.sub_apply]
  ring

private theorem exists_smoothDiffQuotDeriv_bound_Icc {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hF' : deriv F 0 = 0) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖smoothDiffQuotDeriv F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_quadratic_bound_of_contDiff_two hF hF'
  obtain ⟨D, hD⟩ := exists_linear_bound_deriv_of_contDiff_two hF hF'
  have hCnn : 0 ≤ C := (norm_nonneg (F 1 - F 0)).trans (by simpa using hC 1 (by simp))
  have hDnn : 0 ≤ D := (norm_nonneg (deriv F 1)).trans (by simpa using hD 1 (by simp))
  refine ⟨C + D, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [smoothDiffQuotDeriv, add_nonneg hCnn hDnn]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hnum : ‖F x - F 0 - (x : ℂ) * deriv F x‖ ≤ (C + D) * x ^ 2 := by
    calc
      ‖F x - F 0 - (x : ℂ) * deriv F x‖
          ≤ ‖F x - F 0‖ + ‖(x : ℂ) * deriv F x‖ := norm_sub_le _ _
      _ ≤ C * x ^ 2 + x * (D * x) := by
        gcongr
        · exact hC x hx
        · rw [norm_mul]
          rw [Complex.norm_real x, Real.norm_eq_abs, abs_of_pos hxpos]
          gcongr
          exact hD x hx
      _ = (C + D) * x ^ 2 := by ring
  rw [smoothDiffQuotDeriv, norm_div, norm_pow]
  rw [Complex.norm_real x, Real.norm_eq_abs, abs_of_pos hxpos,
    div_le_iff₀ (pow_pos hxpos 2)]
  simpa only [pow_two] using hnum

private theorem integrableOn_smoothDiffQuotDeriv_Icc {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hF' : deriv F 0 = 0) :
    IntegrableOn (smoothDiffQuotDeriv F) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨C, hC⟩ := exists_smoothDiffQuotDeriv_bound_Icc hF hF'
  have hCnn : 0 ≤ C := (norm_nonneg (smoothDiffQuotDeriv F 0)).trans (hC 0 (by simp))
  refine Integrable.mono'
    (MeasureTheory.integrableOn_const (C := (C : ℝ)) (measure_Icc_lt_top.ne))
    ?_ ?_
  · have hcontDeriv : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
    have hmeas : Measurable (smoothDiffQuotDeriv F) := by
      unfold smoothDiffQuotDeriv
      exact ((hF.continuous.sub continuous_const).sub
        (Complex.continuous_ofReal.mul hcontDeriv)).measurable.div
          (Complex.continuous_ofReal.pow 2).measurable
    exact hmeas.aestronglyMeasurable.restrict
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hCnn] using hC x hx

private theorem integrableOn_complex_inv_sq_Ici_one :
    IntegrableOn (fun x : ℝ => ((x : ℂ) ^ 2)⁻¹) (Set.Ici (1 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hreal : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  refine IntegrableOn.congr_fun hreal.ofReal (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 ≤ x := le_trans zero_le_one hx.le
  rw [Real.rpow_neg hx0, Real.rpow_two]
  push_cast
  rfl

private theorem integrableOn_smoothDiffQuotDeriv_Ici_one {F : ℝ → ℂ}
    (hFint : Integrable F) (hFderiv : Integrable (deriv F)) :
    IntegrableOn (smoothDiffQuotDeriv F) (Set.Ici (1 : ℝ)) := by
  have hinv_meas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ)⁻¹)
      (volume.restrict (Set.Ici (1 : ℝ))) :=
    Complex.measurable_ofReal.inv.aestronglyMeasurable.restrict
  have hinv_bound : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖(x : ℂ)⁻¹‖ ≤ 1 := by
    refine (ae_restrict_iff' measurableSet_Ici).2
      (Filter.Eventually.of_forall (fun (x : ℝ) hx => ?_))
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hx)]
    exact (inv_le_one₀ (zero_lt_one.trans_le hx)).2 hx
  have hderiv_div : IntegrableOn (fun x : ℝ => deriv F x / (x : ℂ)) (Set.Ici 1) := by
    have h := hFderiv.integrableOn.bdd_mul (c := 1) hinv_meas hinv_bound
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [div_eq_mul_inv]
    exact mul_comm _ _
  have hinv_sq_meas : AEStronglyMeasurable (fun x : ℝ => ((x : ℂ) ^ 2)⁻¹)
      (volume.restrict (Set.Ici (1 : ℝ))) :=
    (Complex.measurable_ofReal.pow_const 2).inv.aestronglyMeasurable.restrict
  have hinv_sq_bound : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖((x : ℂ) ^ 2)⁻¹‖ ≤ 1 := by
    refine (ae_restrict_iff' measurableSet_Ici).2
      (Filter.Eventually.of_forall (fun (x : ℝ) hx => ?_))
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans_le hx)]
    have hxpow : 1 ≤ x ^ 2 := one_le_pow₀ hx
    exact (inv_le_one₀ (pow_pos (zero_lt_one.trans_le hx) 2)).2 hxpow
  have hF_div_sq : IntegrableOn (fun x : ℝ => F x / (x : ℂ) ^ 2) (Set.Ici 1) := by
    have h := hFint.integrableOn.mul_bdd (c := 1) hinv_sq_meas hinv_sq_bound
    change Integrable (fun x : ℝ => F x / (x : ℂ) ^ 2)
      (volume.restrict (Set.Ici (1 : ℝ)))
    simpa only [div_eq_mul_inv] using h
  have hconst_div_sq : IntegrableOn (fun x : ℝ => F 0 / (x : ℂ) ^ 2) (Set.Ici 1) := by
    change Integrable (fun x : ℝ => F 0 / (x : ℂ) ^ 2)
      (volume.restrict (Set.Ici (1 : ℝ)))
    simpa only [div_eq_mul_inv] using integrableOn_complex_inv_sq_Ici_one.const_mul (F 0)
  have hsum := hderiv_div.neg.add (hF_div_sq.sub hconst_div_sq)
  refine hsum.congr_fun (fun x hx => ?_) measurableSet_Ici
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le hx))
  unfold smoothDiffQuotDeriv
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, div_eq_mul_inv]
  field_simp [hxc]
  ring

private theorem integrableOn_smoothDiffQuotDeriv_Ici {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hF' : deriv F 0 = 0)
    (hFint : Integrable F) (hFderiv : Integrable (deriv F)) :
    IntegrableOn (smoothDiffQuotDeriv F) (Set.Ici (0 : ℝ)) := by
  have hlocal := integrableOn_smoothDiffQuotDeriv_Icc hF hF'
  have htail := integrableOn_smoothDiffQuotDeriv_Ici_one hFint hFderiv
  rw [show Set.Ici (0 : ℝ) = Set.Icc 0 1 ∪ Set.Ici 1 by
    exact (Set.Icc_union_Ici_eq_Ici zero_le_one).symm]
  exact hlocal.union htail

private theorem boundedVariationOn_smoothDiffQuot {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hF' : deriv F 0 = 0)
    (hFint : Integrable F) (hFderiv : Integrable (deriv F)) :
    BoundedVariationOn (smoothDiffQuot F) (Set.Ici 0) := by
  apply DedekindResidue.boundedVariationOn_of_deriv_integrable Set.ordConnected_Ici
    (continuous_smoothDiffQuot (hF.differentiable (by norm_num)) hF').continuousOn
  · rw [interior_Ici]
    intro x hx
    exact hasDerivAt_smoothDiffQuot (hF.differentiable (by norm_num)) (ne_of_gt hx)
  · exact integrableOn_smoothDiffQuotDeriv_Ici hF hF' hFint hFderiv

private theorem deriv_zero_of_even' (F : ℝ → ℂ) (hF : Differentiable ℝ F)
    (hFeven : Function.Even F) : deriv F 0 = 0 := by
  have hderiv := (hF 0).hasDerivAt
  have hderivAtNeg : HasDerivAt F (deriv F 0) (-0) := by simpa using hderiv
  have hderivNeg := HasDerivAt.scomp (𝕜 := ℝ) 0 hderivAtNeg (hasDerivAt_neg 0)
  have hcomp : F ∘ Neg.neg = F := by
    funext x
    exact hFeven x
  rw [hcomp] at hderivNeg
  have hunique := hderiv.unique hderivNeg
  have hunique' : deriv F 0 = -deriv F 0 := by simpa using hunique
  exact CharZero.eq_neg_self_iff.mp hunique'

private theorem deriv_complexify_eq (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    deriv (complexify f) = complexify (deriv f) := by
  funext x
  exact (hf x).hasDerivAt.ofReal_comp.deriv

theorem boundedVariationOn_poitouDiffQuot_scaledTartarNumerator {a : ℝ} (ha : a ≠ 0) :
    BoundedVariationOn (poitouDiffQuot (scaledNumerator tartarNumerator a))
      (Set.Ici 0) := by
  let f := scaledNumerator tartarNumerator a
  let F := complexify f
  have hfcont : ContDiff ℝ ∞ f := contDiff_scaledTartarNumerator a
  have hFcont : ContDiff ℝ 2 F :=
    Complex.ofRealCLM.contDiff.comp (hfcont.of_le (by simp))
  have hfeven : Function.Even f := by
    intro x
    simpa only [f, scaledNumerator, neg_div] using tartarNumerator_even (x / a)
  have hFeven : Function.Even F := fun x ↦ congrArg Complex.ofReal (hfeven x)
  have hFzero : deriv F 0 = 0 :=
    deriv_zero_of_even' F (hFcont.differentiable (by norm_num)) hFeven
  have hfint : Integrable f :=
    (integrable_comp_div_iff tartarNumerator ha).2 integrable_tartarNumerator
  have hFint : Integrable F := hfint.ofReal
  have hFderiv : Integrable (deriv F) := by
    rw [deriv_complexify_eq f (hfcont.differentiable (by simp))]
    exact (integrable_deriv_scaledTartarNumerator ha).ofReal
  have h := boundedVariationOn_smoothDiffQuot hFcont hFzero hFint hFderiv
  have heq : smoothDiffQuot F = poitouDiffQuot f := by
    funext x
    simp only [smoothDiffQuot, F, complexify, poitouDiffQuot]
    push_cast
    rfl
  rwa [heq] at h

private noncomputable def poitouKernelDeriv (f : ℝ → ℝ) : ℝ → ℂ :=
  fun x ↦ ((deriv f x / Real.cosh (x / 2) -
    f x * Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2) : ℝ) : ℂ)

private theorem one_le_cosh (x : ℝ) : 1 ≤ Real.cosh x := by
  nlinarith [Real.cosh_sq x, sq_nonneg (Real.sinh x), Real.cosh_pos x]

private theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [abs_le]
  constructor
  · have h := Real.sinh_lt_cosh (-x)
    have := neg_le_neg h.le
    simpa using this
  · exact (Real.sinh_lt_cosh x).le

private theorem integrable_poitouKernelDeriv {f : ℝ → ℝ}
    (hf : Integrable f) (hfderiv : Integrable (deriv f)) :
    Integrable (poitouKernelDeriv f) := by
  have hweight_cont : Continuous (fun x : ℝ ↦ 1 / Real.cosh (x / 2)) :=
    continuous_const.div (Real.continuous_cosh.comp (continuous_id.div_const 2))
      (fun x ↦ (Real.cosh_pos _).ne')
  have hweight_bound : ∀ x : ℝ, ‖1 / Real.cosh (x / 2)‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_pos (Real.cosh_pos _)]
    exact (div_le_one (Real.cosh_pos _)).2 (one_le_cosh _)
  have hfirst : Integrable (fun x : ℝ ↦ deriv f x * (1 / Real.cosh (x / 2))) := by
    exact Integrable.mul_bdd (c := 1) hfderiv hweight_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hweight_bound)
  have hderivWeight_cont : Continuous (fun x : ℝ ↦
      Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2)) := by
    exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).div
      (continuous_const.mul ((Real.continuous_cosh.comp
        (continuous_id.div_const 2)).pow 2))
      (fun x ↦ mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
  have hderivWeight_bound : ∀ x : ℝ,
      ‖Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2)‖ ≤ 1 / 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_pos (Real.cosh_pos _), div_le_iff₀ (by positivity)]
    norm_num
    have hs := abs_sinh_le_cosh (x / 2)
    have hc := one_le_cosh (x / 2)
    nlinarith
  have hsecond : Integrable (fun x : ℝ ↦
      f x * (Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2))) := by
    exact Integrable.mul_bdd (c := 1 / 2) hf hderivWeight_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hderivWeight_bound)
  have hreal : Integrable (fun x : ℝ ↦ deriv f x * (1 / Real.cosh (x / 2)) -
      f x * (Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2))) := by
    refine (hfirst.sub hsecond).congr (Filter.Eventually.of_forall (fun x ↦ ?_))
    rfl
  have heq :
      (fun x : ℝ ↦ deriv f x * (1 / Real.cosh (x / 2)) -
        f x * (Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2))) =
      fun x : ℝ ↦ deriv f x / Real.cosh (x / 2) -
        f x * Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2) := by
    funext x
    ring
  rw [heq] at hreal
  exact hreal.ofReal

private theorem hasDerivAt_poitouKernel {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (x : ℝ) : HasDerivAt (poitouKernel f) (poitouKernelDeriv f x) x := by
  have hcosh : HasDerivAt (fun u : ℝ ↦ Real.cosh (u / 2))
      (Real.sinh (x / 2) / 2) x := by
    simpa only [id_eq, div_eq_mul_inv, one_mul] using
      ((hasDerivAt_id x).div_const 2).cosh
  have hreal := (hf x).hasDerivAt.div hcosh (Real.cosh_pos (x / 2)).ne'
  have hcomplex := hreal.ofReal_comp
  refine hcomplex.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun _ ↦ rfl)) |>.congr_deriv ?_
  simp only [poitouKernelDeriv]
  push_cast
  field_simp [(Real.cosh_pos (x / 2)).ne']

theorem boundedVariationOn_poitouKernel_scaledTartarNumerator {a : ℝ} (ha : a ≠ 0) :
    BoundedVariationOn (poitouKernel (scaledNumerator tartarNumerator a))
      (Set.Ici 0) := by
  let f := scaledNumerator tartarNumerator a
  have hfcont : ContDiff ℝ ∞ f := contDiff_scaledTartarNumerator a
  have hfint : Integrable f :=
    (integrable_comp_div_iff tartarNumerator ha).2 integrable_tartarNumerator
  apply DedekindResidue.boundedVariationOn_of_deriv_integrable Set.ordConnected_Ici
  · exact (Complex.ofRealCLM.continuous.comp
      (hfcont.continuous.div (Real.continuous_cosh.comp (continuous_id.div_const 2))
        (fun x ↦ (Real.cosh_pos _).ne'))).continuousOn
  · rw [interior_Ici]
    intro x _
    exact hasDerivAt_poitouKernel (hfcont.differentiable (by simp)) x
  · exact (integrable_poitouKernelDeriv hfint
      (integrable_deriv_scaledTartarNumerator ha)).integrableOn

theorem scaledTartar_isPoitouTestFn_unconditional {y : ℝ} (hy : 0 < y) :
    IsPoitouTestFn (scaledNumerator tartarNumerator (1 / √y)) := by
  have hscale : (1 / √y : ℝ) ≠ 0 := one_div_ne_zero (Real.sqrt_ne_zero'.2 hy)
  exact scaledTartar_isPoitouTestFn hy
    (boundedVariationOn_poitouKernel_scaledTartarNumerator hscale)
    (boundedVariationOn_poitouDiffQuot_scaledTartarNumerator hscale)

end Odlyzko
