/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouAdmissibility

/-!
# Poitou boundary values

The factor `cosh (x / 2)` in Poitou's kernel converts both vertical boundary values of
`paperPhi` into the Fourier transform of its real numerator.  This file proves that
identity and computes the two pole values for the scaled Tartar numerator.
-/

@[expose] public section

open MeasureTheory Filter
open scoped FourierTransform

namespace Odlyzko

private theorem integrable_comp_neg_real {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun x : ℝ ↦ f (-x)) := by
  simpa only [Function.comp_def] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hf

private theorem integral_eq_of_add_comp_neg_eq_two_mul {g h : ℝ → ℝ}
    (hg : Integrable g) (heq : ∀ x, g x + g (-x) = 2 * h x) :
    ∫ x : ℝ, g x = ∫ x : ℝ, h x := by
  have hgneg : Integrable (fun x : ℝ ↦ g (-x)) := integrable_comp_neg_real hg
  have hint : (∫ x : ℝ, g (-x)) = ∫ x : ℝ, g x := by
    exact_mod_cast DedekindResidue.integral_comp_neg_real (fun x ↦ (g x : ℂ))
  calc
    ∫ x : ℝ, g x = ((∫ x : ℝ, g x) + ∫ x : ℝ, g (-x)) / 2 := by
      rw [hint]
      ring
    _ = ∫ x : ℝ, (g x + g (-x)) / 2 := by
      rw [integral_div, integral_add hg hgneg]
    _ = ∫ x : ℝ, h x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by
        simp only
        rw [heq x]
        ring)

private theorem integrable_fourierReal (f : ℝ → ℝ) (hf : Integrable f) (γ : ℝ) :
    Integrable (fun x : ℝ ↦ f x * Real.cos (γ * x)) := by
  apply hf.mul_bdd (c := 1)
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

/-- The real part of the Fourier transform of a real function is its cosine transform. -/
theorem fourier_complexify_re_eq_integral_cos (f : ℝ → ℝ)
    (hf : Integrable f) (γ : ℝ) :
    (𝓕 (complexify f) (poitouFourierFrequency γ)).re =
      ∫ x : ℝ, f x * Real.cos (γ * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint : Integrable (fun x : ℝ ↦
      Complex.exp ((-2 * Real.pi * x * poitouFourierFrequency γ : ℝ) * Complex.I) •
        complexify f x) := by
    apply Integrable.bdd_mul (c := 1) hf.ofReal
    · exact (by fun_prop : Continuous (fun x : ℝ ↦ Complex.exp
          ((-2 * Real.pi * x * poitouFourierFrequency γ : ℝ) *
            Complex.I))).aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_exp, Complex.mul_re]
      simp
  calc
    (∫ x : ℝ, Complex.exp
        ((-2 * Real.pi * x * poitouFourierFrequency γ : ℝ) * Complex.I) •
          complexify f x).re =
        ∫ x : ℝ, (Complex.exp
          ((-2 * Real.pi * x * poitouFourierFrequency γ : ℝ) * Complex.I) •
            complexify f x).re := (integral_re hint).symm
    _ = ∫ x : ℝ, f x * Real.cos (γ * x) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun x ↦ ?_)
      change (Complex.exp (((-2 * Real.pi * x * poitouFourierFrequency γ : ℝ) : ℂ) *
        Complex.I) • complexify f x).re = f x * Real.cos (γ * x)
      rw [show -2 * Real.pi * x * poitouFourierFrequency γ = x * γ by
        rw [poitouFourierFrequency]
        field_simp [show (2 * Real.pi : ℝ) ≠ 0 by positivity]]
      change (Complex.exp (((x * γ : ℝ) : ℂ) * Complex.I) * complexify f x).re =
        f x * Real.cos (γ * x)
      simp only [complexify, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
      simp [mul_comm]

private theorem integrable_paperPhi_poitouKernel_lower
    (f : ℝ → ℝ) (hf : Integrable f) (γ : ℝ) :
    Integrable (fun x : ℝ ↦ poitouKernel f x *
      Complex.exp ((γ * Complex.I - 1 / 2) * x)) := by
  have hfactor_cont : Continuous (fun x : ℝ ↦
      Complex.exp ((γ * Complex.I - 1 / 2) * x) /
        Real.cosh (x / 2)) := by
    exact (Complex.continuous_exp.comp (by fun_prop)).div
      (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp
        (continuous_id.div_const 2))) (fun x ↦ by
          exact_mod_cast (Real.cosh_pos (x / 2)).ne')
  have hfactor_bound : ∀ x : ℝ, ‖Complex.exp
      ((γ * Complex.I - 1 / 2) * x) /
        Real.cosh (x / 2)‖ ≤ 2 := by
    intro x
    rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
    rw [show (((γ * Complex.I - 1 / 2) * x)).re =
        -(x / 2) by simp [Complex.mul_re]; ring, Real.cosh_eq]
    have hpos := Real.exp_pos (x / 2)
    have hposneg := Real.exp_pos (-(x / 2))
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hprod := Integrable.mul_bdd (c := 2) hf.ofReal hfactor_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall hfactor_bound)
  refine hprod.congr (Filter.Eventually.of_forall (fun x ↦ ?_))
  simp only [poitouKernel_apply]
  rw [Complex.ofReal_div]
  calc
    (f x : ℂ) * (Complex.exp ((γ * Complex.I - 1 / 2) * x) /
        Real.cosh (x / 2)) =
        (f x : ℂ) * Complex.exp ((γ * Complex.I - 1 / 2) * x) /
          Real.cosh (x / 2) := (mul_div_assoc _ _ _).symm
    _ = (f x : ℂ) / Real.cosh (x / 2) *
        Complex.exp ((γ * Complex.I - 1 / 2) * x) :=
      (div_mul_eq_mul_div _ _ _).symm

private theorem integrable_paperPhi_poitouKernel_upper
    (f : ℝ → ℝ) (hf : Integrable f) (γ : ℝ) :
    Integrable (fun x : ℝ ↦ poitouKernel f x *
      Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x)) := by
  have hfactor_cont : Continuous (fun x : ℝ ↦
      Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x) /
        Real.cosh (x / 2)) := by
    exact (Complex.continuous_exp.comp (by fun_prop)).div
      (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp
        (continuous_id.div_const 2))) (fun x ↦ by
          exact_mod_cast (Real.cosh_pos (x / 2)).ne')
  have hfactor_bound : ∀ x : ℝ, ‖Complex.exp
      (((1 : ℂ) + γ * Complex.I - 1 / 2) * x) /
        Real.cosh (x / 2)‖ ≤ 2 := by
    intro x
    rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _)]
    rw [show ((((1 : ℂ) + γ * Complex.I - 1 / 2) * x)).re =
        x / 2 by simp [Complex.mul_re]; ring, Real.cosh_eq]
    have hpos := Real.exp_pos (x / 2)
    have hposneg := Real.exp_pos (-(x / 2))
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hprod := Integrable.mul_bdd (c := 2) hf.ofReal hfactor_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall hfactor_bound)
  refine hprod.congr (Filter.Eventually.of_forall (fun x ↦ ?_))
  simp only [poitouKernel_apply]
  rw [Complex.ofReal_div]
  calc
    (f x : ℂ) * (Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x) /
        Real.cosh (x / 2)) =
        (f x : ℂ) * Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x) /
          Real.cosh (x / 2) := (mul_div_assoc _ _ _).symm
    _ = (f x : ℂ) / Real.cosh (x / 2) *
        Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x) :=
      (div_mul_eq_mul_div _ _ _).symm

private theorem re_poitouKernel_mul_exp_lower (f : ℝ → ℝ) (γ x : ℝ) :
    (poitouKernel f x * Complex.exp ((γ * Complex.I - 1 / 2) * x)).re =
      f x / Real.cosh (x / 2) * Real.exp (-(x / 2)) * Real.cos (γ * x) := by
  rw [Complex.mul_re]
  simp only [poitouKernel_apply, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_re]
  rw [show ((γ * Complex.I - 1 / 2) * x).re = -(x / 2) by
    simp [Complex.mul_re]; ring]
  rw [show ((γ * Complex.I - 1 / 2) * x).im = γ * x by
    simp [Complex.mul_im]]
  ring

private theorem re_poitouKernel_mul_exp_upper (f : ℝ → ℝ) (γ x : ℝ) :
    (poitouKernel f x * Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x)).re =
      f x / Real.cosh (x / 2) * Real.exp (x / 2) * Real.cos (γ * x) := by
  rw [Complex.mul_re]
  simp only [poitouKernel_apply, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_re]
  rw [show (((1 : ℂ) + γ * Complex.I - 1 / 2) * x).re = x / 2 by
    simp [Complex.mul_re]; ring]
  rw [show (((1 : ℂ) + γ * Complex.I - 1 / 2) * x).im = γ * x by
    simp [Complex.mul_im]]
  ring

private theorem lower_boundary_pair (f : ℝ → ℝ) (heven : Function.Even f)
    (γ x : ℝ) :
    (poitouKernel f x * Complex.exp ((γ * Complex.I - 1 / 2) * x)).re +
        (poitouKernel f (-x) *
          Complex.exp ((γ * Complex.I - 1 / 2) * ((-x : ℝ) : ℂ))).re =
      2 * (f x * Real.cos (γ * x)) := by
  rw [re_poitouKernel_mul_exp_lower f γ x]
  have hneg := re_poitouKernel_mul_exp_lower f γ (-x)
  simp only [neg_div, neg_neg] at hneg
  rw [hneg]
  rw [heven x]
  simp only [Real.cosh_neg, mul_neg, Real.cos_neg]
  rw [Real.cosh_eq]
  field_simp [show Real.exp (x / 2) + Real.exp (-(x / 2)) ≠ 0 by positivity]
  ring

private theorem upper_boundary_pair (f : ℝ → ℝ) (heven : Function.Even f)
    (γ x : ℝ) :
    (poitouKernel f x *
        Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x)).re +
        (poitouKernel f (-x) *
          Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * ((-x : ℝ) : ℂ))).re =
      2 * (f x * Real.cos (γ * x)) := by
  rw [re_poitouKernel_mul_exp_upper f γ x]
  have hneg := re_poitouKernel_mul_exp_upper f γ (-x)
  simp only [neg_div] at hneg
  rw [hneg]
  rw [heven x]
  simp only [Real.cosh_neg, mul_neg, Real.cos_neg]
  rw [Real.cosh_eq]
  field_simp [show Real.exp (x / 2) + Real.exp (-(x / 2)) ≠ 0 by positivity]

/-- Poitou's hyperbolic denominator turns both vertical boundary values into the
Fourier transform of the numerator. -/
theorem paperPhi_poitouKernel_boundaryIdentification (f : ℝ → ℝ)
    (hf : Integrable f) (heven : Function.Even f) :
    PoitouBoundaryIdentification (DedekindResidue.paperPhi (poitouKernel f)) f := by
  constructor
  · intro γ
    rw [DedekindResidue.paperPhi]
    have hint := integrable_paperPhi_poitouKernel_lower f hf γ
    calc
      (∫ x : ℝ, poitouKernel f x *
          Complex.exp ((γ * Complex.I - 1 / 2) * x)).re =
          ∫ x : ℝ, (poitouKernel f x *
            Complex.exp ((γ * Complex.I - 1 / 2) * x)).re := (integral_re hint).symm
      _ = ∫ x : ℝ, f x * Real.cos (γ * x) :=
        integral_eq_of_add_comp_neg_eq_two_mul hint.re
          (lower_boundary_pair f heven γ)
      _ = (𝓕 (complexify f) (poitouFourierFrequency γ)).re :=
        (fourier_complexify_re_eq_integral_cos f hf γ).symm
  · intro γ
    rw [DedekindResidue.paperPhi]
    have hint := integrable_paperPhi_poitouKernel_upper f hf γ
    calc
      (∫ x : ℝ, poitouKernel f x *
          Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x)).re =
          ∫ x : ℝ, (poitouKernel f x *
            Complex.exp (((1 : ℂ) + γ * Complex.I - 1 / 2) * x)).re :=
        (integral_re hint).symm
      _ = ∫ x : ℝ, f x * Real.cos (γ * x) :=
        integral_eq_of_add_comp_neg_eq_two_mul hint.re
          (upper_boundary_pair f heven γ)
      _ = (𝓕 (complexify f) (poitouFourierFrequency γ)).re :=
        (fourier_complexify_re_eq_integral_cos f hf γ).symm

/-- The two pole values contribute twice the total mass of an even Poitou numerator. -/
theorem paperPhi_poitouKernel_zero_add_one_re (f : ℝ → ℝ)
    (hf : Integrable f) (heven : Function.Even f) :
    (DedekindResidue.paperPhi (poitouKernel f) 0 +
      DedekindResidue.paperPhi (poitouKernel f) 1).re = 2 * ∫ x : ℝ, f x := by
  have hboundary := paperPhi_poitouKernel_boundaryIdentification f hf heven
  have hlower : (DedekindResidue.paperPhi (poitouKernel f) 0).re =
      (𝓕 (complexify f) (poitouFourierFrequency 0)).re := by
    simpa using hboundary.lower 0
  have hupper : (DedekindResidue.paperPhi (poitouKernel f) 1).re =
      (𝓕 (complexify f) (poitouFourierFrequency 0)).re := by
    simpa using hboundary.upper 0
  rw [Complex.add_re, hlower, hupper,
    fourier_complexify_re_eq_integral_cos f hf 0]
  simp
  ring

/-- Boundary identification for every Gaussian approximant of the scaled Tartar numerator. -/
theorem gaussianPoitouApproximant_scaledTartar_boundaryIdentification
    {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    PoitouBoundaryIdentification
      (DedekindResidue.paperPhi
        (gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n))
      (gaussianDampedNumerator (scaledNumerator tartarNumerator a) n) := by
  have hfint : Integrable (scaledNumerator tartarNumerator a) :=
    (integrable_comp_div_iff tartarNumerator ha).2 integrable_tartarNumerator
  have hfeven : Function.Even (scaledNumerator tartarNumerator a) := by
    intro x
    simpa only [scaledNumerator, neg_div] using tartarNumerator_even (x / a)
  simpa only [gaussianPoitouApproximant] using
    paperPhi_poitouKernel_boundaryIdentification
      (gaussianDampedNumerator (scaledNumerator tartarNumerator a) n)
      (Integrable.gaussianDampedNumerator hfint n) (gaussianDampedNumerator_even hfeven n)

/-- The weak scaled Tartar kernel has the same boundary identification as its approximants. -/
theorem scaledTartar_boundaryIdentification {y : ℝ} (hy : 0 < y) :
    PoitouBoundaryIdentification
      (DedekindResidue.paperPhi
        (poitouKernel (scaledNumerator tartarNumerator (1 / √y))))
      (scaledNumerator tartarNumerator (1 / √y)) := by
  have hscale : 0 < 1 / √y := by positivity
  have hfint : Integrable (scaledNumerator tartarNumerator (1 / √y)) :=
    (integrable_comp_div_iff tartarNumerator hscale.ne').2 integrable_tartarNumerator
  have hfeven : Function.Even (scaledNumerator tartarNumerator (1 / √y)) := by
    intro x
    simpa only [scaledNumerator, neg_div] using tartarNumerator_even (x / (1 / √y))
  exact paperPhi_poitouKernel_boundaryIdentification _ hfint hfeven

/-- The two pole values of the Gaussian approximants converge to the scaled
Tartar pole correction. -/
theorem tendsto_gaussianPoitouApproximant_scaledTartar_poleCorrection
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ =>
      (DedekindResidue.paperPhi
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n) 0 +
        DedekindResidue.paperPhi
          (gaussianPoitouApproximant
            (scaledNumerator tartarNumerator (1 / √y)) n) 1).re)
      atTop (nhds (12 * Real.pi / (5 * √y))) := by
  let f := scaledNumerator tartarNumerator (1 / √y)
  have hscale : 0 < 1 / √y := by positivity
  have hf : Integrable f :=
    (integrable_comp_div_iff tartarNumerator hscale.ne').2 integrable_tartarNumerator
  have hf0 : ∀ x, 0 ≤ f x := fun x => tartarNumerator_nonneg _
  have hmeas (n : ℕ) : AEStronglyMeasurable (gaussianDampedNumerator f n) :=
    hf.aestronglyMeasurable.mul (continuous_poitouGaussianCutoff n).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x, ‖gaussianDampedNumerator f n x‖ ≤ f x :=
    Filter.Eventually.of_forall fun x => by
      rw [gaussianDampedNumerator, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hf0 x) (poitouGaussianCutoff_pos n x).le)]
      exact mul_le_of_le_one_right (hf0 x) (poitouGaussianCutoff_le_one n x)
  have hlim : ∀ᵐ x, Tendsto (fun n => gaussianDampedNumerator f n x)
      atTop (nhds (f x)) :=
    Filter.Eventually.of_forall fun x => tendsto_gaussianDampedNumerator f x
  have hint := tendsto_integral_of_dominated_convergence f hmeas hf hbound hlim
  have hpole (n : ℕ) :
      (DedekindResidue.paperPhi (gaussianPoitouApproximant f n) 0 +
        DedekindResidue.paperPhi (gaussianPoitouApproximant f n) 1).re =
        2 * ∫ x : ℝ, gaussianDampedNumerator f n x := by
    simpa only [gaussianPoitouApproximant] using
      paperPhi_poitouKernel_zero_add_one_re
        (gaussianDampedNumerator f n)
        (Integrable.gaussianDampedNumerator hf n)
        (gaussianDampedNumerator_even (fun x => by
          dsimp [f, scaledNumerator]
          simpa only [neg_div] using tartarNumerator_even (x / (1 / √y))) n)
  have hmass : (∫ x : ℝ, f x) = (1 / √y) * (6 * Real.pi / 5) := by
    change (∫ x : ℝ, tartarNumerator (x / (1 / √y))) = _
    rw [MeasureTheory.Measure.integral_comp_div, abs_of_pos hscale,
      integral_tartarNumerator]
    rfl
  convert hint.const_mul 2 using 1
  · funext n
    exact hpole n
  · rw [hmass]
    congr 1
    ring

/-- Poitou's scaled Tartar kernel contributes `12π/(5√y)` at the two poles. -/
theorem scaledTartar_poleCorrection {y : ℝ} (hy : 0 < y) :
    (DedekindResidue.paperPhi
        (poitouKernel (scaledNumerator tartarNumerator (1 / √y))) 0 +
      DedekindResidue.paperPhi
        (poitouKernel (scaledNumerator tartarNumerator (1 / √y))) 1).re =
      12 * Real.pi / (5 * √y) := by
  have hscale : 0 < 1 / √y := by positivity
  have hfint : Integrable (scaledNumerator tartarNumerator (1 / √y)) :=
    (integrable_comp_div_iff tartarNumerator hscale.ne').2 integrable_tartarNumerator
  have hfeven : Function.Even (scaledNumerator tartarNumerator (1 / √y)) := by
    intro x
    simpa only [scaledNumerator, neg_div] using tartarNumerator_even (x / (1 / √y))
  have hmass : (∫ x : ℝ, scaledNumerator tartarNumerator (1 / √y) x) =
      (1 / √y) * (6 * Real.pi / 5) := by
    change (∫ x : ℝ, tartarNumerator (x / (1 / √y))) = _
    rw [MeasureTheory.Measure.integral_comp_div, abs_of_pos hscale,
      integral_tartarNumerator]
    rfl
  rw [paperPhi_poitouKernel_zero_add_one_re _ hfint hfeven, hmass]
  field_simp [Real.sqrt_ne_zero'.2 hy]
  ring

end Odlyzko
