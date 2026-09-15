/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouRegularization
public import FLT.Odlyzko.FourierProduct
public import FLT.Odlyzko.TartarPlancherel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian regularization of Poitou kernels

Multiplying a Poitou numerator by `exp (-x²/(n+1))` supplies the strict decay margin needed by
the strong explicit-formula test class.  This file begins the concrete regularization by recording
the damping family, its structural properties, and pointwise convergence of the resulting kernels.
-/

@[expose] public section

open Filter MeasureTheory
open scoped FourierTransform Topology

namespace Odlyzko

/-- The Gaussian cutoff with variance tending to infinity. -/
noncomputable def poitouGaussianCutoff (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / ((n : ℝ) + 1))

/-- A numerator damped by a Gaussian whose variance tends to infinity. -/
noncomputable def gaussianDampedNumerator (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f x * poitouGaussianCutoff n x

/-- The corresponding strong candidate for the explicit formula. -/
noncomputable def gaussianPoitouApproximant (f : ℝ → ℝ) (n : ℕ) : ℝ → ℂ :=
  poitouKernel (gaussianDampedNumerator f n)

@[simp] theorem poitouGaussianCutoff_zero (n : ℕ) : poitouGaussianCutoff n 0 = 1 := by
  simp [poitouGaussianCutoff]

theorem poitouGaussianCutoff_pos (n : ℕ) (x : ℝ) : 0 < poitouGaussianCutoff n x := by
  exact Real.exp_pos _

theorem poitouGaussianCutoff_le_one (n : ℕ) (x : ℝ) : poitouGaussianCutoff n x ≤ 1 := by
  rw [poitouGaussianCutoff, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by positivity)

/-- Every Gaussian cutoff is integrable. -/
theorem integrable_poitouGaussianCutoff (n : ℕ) : Integrable (poitouGaussianCutoff n) := by
  have hcoef : 0 < 1 / ((n : ℝ) + 1) := by positivity
  convert integrable_exp_neg_mul_sq hcoef using 1
  funext x
  rw [poitouGaussianCutoff]
  congr 1
  field_simp

theorem poitouGaussianCutoff_even (n : ℕ) : Function.Even (poitouGaussianCutoff n) := by
  intro x
  simp [poitouGaussianCutoff]

theorem continuous_poitouGaussianCutoff (n : ℕ) : Continuous (poitouGaussianCutoff n) := by
  unfold poitouGaussianCutoff
  fun_prop

/-- The Fourier transform of every Gaussian cutoff is nonnegative. -/
theorem fourier_poitouGaussianCutoff_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ (𝓕 (complexify (poitouGaussianCutoff n)) t).re := by
  let b : ℝ := 1 / ((n : ℝ) + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hfun : complexify (poitouGaussianCutoff n) =
      fun x : ℝ ↦ Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    simp only [complexify, poitouGaussianCutoff, Real.norm_eq_abs]
    rw [show (-x ^ 2 / ((n : ℝ) + 1) : ℝ) = -b * |x| ^ 2 by
      rw [sq_abs]
      dsimp [b]
      field_simp]
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  rw [hfun]
  have htransform :
      𝓕 (fun x : ℝ ↦ Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2)) =
        fun t : ℝ ↦ ((Real.pi : ℂ) / b) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
          Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / b) := by
    funext t
    exact fourier_gaussian_innerProductSpace (V := ℝ) (by simpa using hb) t
  rw [htransform]
  simp only [Module.finrank_self, Nat.cast_one]
  rw [show ((Real.pi : ℂ) / (b : ℂ)) = ((Real.pi / b : ℝ) : ℂ) by push_cast; rfl,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / b) (1 / 2)]
  rw [show (-(Real.pi : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / (b : ℂ)) =
      ((-Real.pi ^ 2 * ‖t‖ ^ 2 / b : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_re,
    Complex.exp_ofReal_im, mul_zero, sub_zero]
  positivity

/-- The Fourier transform of every Gaussian cutoff is integrable. -/
theorem integrable_fourier_poitouGaussianCutoff (n : ℕ) :
    Integrable (𝓕 (complexify (poitouGaussianCutoff n))) := by
  let b : ℝ := 1 / ((n : ℝ) + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hfun : complexify (poitouGaussianCutoff n) =
      fun x : ℝ ↦ Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    simp only [complexify, poitouGaussianCutoff, Real.norm_eq_abs]
    rw [show (-x ^ 2 / ((n : ℝ) + 1) : ℝ) = -b * |x| ^ 2 by
      rw [sq_abs]
      dsimp [b]
      field_simp]
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  rw [hfun]
  have htransform :
      𝓕 (fun x : ℝ ↦ Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2)) =
        fun t : ℝ ↦ ((Real.pi : ℂ) / b) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
          Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / b) := by
    funext t
    exact fourier_gaussian_innerProductSpace (V := ℝ) (by simpa using hb) t
  rw [htransform]
  have hcoef : 0 < (((Real.pi : ℂ) ^ 2 / (b : ℂ))).re := by
    rw [show ((Real.pi : ℂ) ^ 2 / (b : ℂ)) = ((Real.pi ^ 2 / b : ℝ) : ℂ) by
      push_cast
      rfl]
    simp only [Complex.ofReal_re]
    positivity
  convert (integrable_cexp_neg_mul_sq hcoef).const_mul
    (((Real.pi : ℂ) / b) ^ (Module.finrank ℝ ℝ / 2 : ℂ)) using 1
  funext x
  congr 2
  simp only [Real.norm_eq_abs]
  rw [show (((|x| : ℝ) : ℂ) ^ 2) = (((x : ℝ) : ℂ) ^ 2) by
    norm_cast
    exact sq_abs x]
  ring

private theorem fourier_complexify_even_im_eq_zero (f : ℝ → ℝ) (hf : Function.Even f)
    (t : ℝ) : (𝓕 (complexify f) t).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← fourier_reflect_eq_conj]
  apply Real.fourier_congr_ae
  filter_upwards with x
  exact congrArg Complex.ofReal (hf x)

theorem fourier_poitouGaussianCutoff_im_eq_zero (n : ℕ) (t : ℝ) :
    (𝓕 (complexify (poitouGaussianCutoff n)) t).im = 0 :=
  fourier_complexify_even_im_eq_zero _ (poitouGaussianCutoff_even n) t

private theorem integrable_complexify_scaledTartarNumerator {a : ℝ} (ha : a ≠ 0) :
    Integrable (complexify (scaledNumerator tartarNumerator a)) := by
  rw [complexify_scaledNumerator]
  exact (integrable_comp_div_iff (complexify tartarNumerator) ha).2
    integrable_tartarNumerator.ofReal

private theorem continuous_complexify_scaledTartarNumerator (a : ℝ) :
    Continuous (complexify (scaledNumerator tartarNumerator a)) := by
  rw [complexify_scaledNumerator]
  exact continuous_scaled _ _ (Complex.continuous_ofReal.comp continuous_tartarNumerator)

private theorem scaledTartarNumerator_even (a : ℝ) :
    Function.Even (scaledNumerator tartarNumerator a) := by
  intro x
  simpa only [scaledNumerator, neg_div] using tartarNumerator_even (x / a)

private theorem fourier_scaledTartarNumerator_im_eq_zero (a t : ℝ) :
    (𝓕 (complexify (scaledNumerator tartarNumerator a)) t).im = 0 :=
  fourier_complexify_even_im_eq_zero _ (scaledTartarNumerator_even a) t

private theorem integrable_fourier_scaledTartarNumerator {a : ℝ} (ha : 0 < a) :
    Integrable (𝓕 (complexify (scaledNumerator tartarNumerator a))) := by
  have hauto : Integrable (autocorrelation tartarV) :=
    continuous_autocorrelation_tartarV.integrable_of_hasCompactSupport
      hasCompactSupport_autocorrelation_tartarV
  rw [complexify_scaledNumerator]
  have hformula :
      𝓕 (scaled (complexify tartarNumerator) a) = fun t : ℝ ↦
        (a : ℂ) * (9 * Real.pi / 8 : ℂ) *
          autocorrelation tartarV (2 * Real.pi * (a * t)) := by
    funext t
    rw [fourier_scaled _ ha, fourier_tartarNumerator]
    ring
  rw [hformula]
  have hint := ((integrable_comp_div_iff (autocorrelation tartarV)
    (by positivity : (1 / (2 * Real.pi * a) : ℝ) ≠ 0)).2 hauto).const_mul
      ((a : ℂ) * (9 * Real.pi / 8 : ℂ))
  refine hint.congr ?_
  filter_upwards with t
  rw [show t / (1 / (2 * Real.pi * a)) = 2 * Real.pi * (a * t) by
    field_simp]

private theorem hasCompactSupport_fourier_scaledTartarNumerator {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (𝓕 (complexify (scaledNumerator tartarNumerator a))) := by
  rw [complexify_scaledNumerator]
  have hscaled : HasCompactSupport
      (scaled (autocorrelation tartarV) (1 / (2 * Real.pi * a))) :=
    scaled_hasCompactSupport _ (by positivity) hasCompactSupport_autocorrelation_tartarV
  have hformula :
      𝓕 (scaled (complexify tartarNumerator) a) = fun t : ℝ ↦
        (a : ℂ) * (9 * Real.pi / 8 : ℂ) *
          scaled (autocorrelation tartarV) (1 / (2 * Real.pi * a)) t := by
    funext t
    rw [fourier_scaled _ ha, fourier_tartarNumerator]
    simp only [scaled]
    rw [show t / (1 / (2 * Real.pi * a)) = 2 * Real.pi * (a * t) by
      field_simp]
    ring
  rw [hformula]
  change HasCompactSupport
    ((fun _ : ℝ ↦ ((a : ℂ) * (9 * Real.pi / 8 : ℂ))) •
      scaled (autocorrelation tartarV) (1 / (2 * Real.pi * a)))
  exact hscaled.smul_left

/-- At each point the Gaussian cutoff tends to one. -/
theorem tendsto_poitouGaussianCutoff (x : ℝ) :
    Tendsto (fun n ↦ poitouGaussianCutoff n x) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hexponent : Tendsto (fun n : ℕ ↦ -x ^ 2 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [one_div, one_mul, div_eq_mul_inv, mul_zero] using hinv.const_mul (-x ^ 2)
  change Tendsto (Real.exp ∘ fun n : ℕ ↦ -x ^ 2 / ((n : ℝ) + 1)) atTop (nhds 1)
  simpa only [Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp hexponent

@[simp] theorem gaussianDampedNumerator_zero {f : ℝ → ℝ} (hf : f 0 = 1) (n : ℕ) :
    gaussianDampedNumerator f n 0 = 1 := by
  simp [gaussianDampedNumerator, hf]

theorem gaussianDampedNumerator_even {f : ℝ → ℝ} (hf : Function.Even f) (n : ℕ) :
    Function.Even (gaussianDampedNumerator f n) := by
  intro x
  rw [gaussianDampedNumerator, gaussianDampedNumerator, hf,
    poitouGaussianCutoff_even]

theorem gaussianDampedNumerator_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (n : ℕ) (x : ℝ) : 0 ≤ gaussianDampedNumerator f n x :=
  mul_nonneg (hf x) (poitouGaussianCutoff_pos n x).le

/-- Gaussian damping preserves integrability. -/
theorem Integrable.gaussianDampedNumerator {f : ℝ → ℝ} (hf : Integrable f) (n : ℕ) :
    Integrable (gaussianDampedNumerator f n) := by
  apply Integrable.mul_bdd (c := 1) hf
  · exact (continuous_poitouGaussianCutoff n).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (poitouGaussianCutoff_pos n x)]
    exact poitouGaussianCutoff_le_one n x

/-- Gaussian damping preserves Fourier positivity for every positive scaling of the Tartar
numerator. -/
theorem fourier_gaussianDamped_scaledTartar_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) (t : ℝ) :
    0 ≤ (𝓕 (complexify
      (gaussianDampedNumerator (scaledNumerator tartarNumerator a) n)) t).re := by
  let f := complexify (scaledNumerator tartarNumerator a)
  let g := complexify (poitouGaussianCutoff n)
  have hf : Integrable f := integrable_complexify_scaledTartarNumerator ha.ne'
  have hg : Integrable g := integrable_poitouGaussianCutoff n |>.ofReal
  have hF : Integrable (𝓕 f) := integrable_fourier_scaledTartarNumerator ha
  have hG : Integrable (𝓕 g) := integrable_fourier_poitouGaussianCutoff n
  have hproduct : (fun x : ℝ ↦ f x * g x) = complexify
      (gaussianDampedNumerator (scaledNumerator tartarNumerator a) n) := by
    funext x
    simp [f, g, complexify, gaussianDampedNumerator]
  have hfg : Integrable (fun x : ℝ ↦ f x * g x) := by
    rw [hproduct]
    exact (Integrable.gaussianDampedNumerator
      ((integrable_comp_div_iff tartarNumerator ha.ne').2 integrable_tartarNumerator) n).ofReal
  have hfcont : Continuous f := continuous_complexify_scaledTartarNumerator a
  have hgcont : Continuous g :=
    Complex.continuous_ofReal.comp (continuous_poitouGaussianCutoff n)
  have hfeven : Function.Even f := by
    intro x
    exact congrArg Complex.ofReal (scaledTartarNumerator_even a x)
  have hgeven : Function.Even g := by
    intro x
    exact congrArg Complex.ofReal (poitouGaussianCutoff_even n x)
  have hcompact := hasCompactSupport_fourier_scaledTartarNumerator ha
  have hidentity := fourier_mul_eq_convolution_of_even f g hf hg hF hG hfg hfcont hgcont
    hfeven hgeven hcompact
  rw [hproduct] at hidentity
  rw [hidentity]
  exact convolution_re_nonneg_of_nonneg (𝓕 f) (𝓕 g) hcompact
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf)
    hG.locallyIntegrable
    (fourier_scaledNumerator_nonneg tartarNumerator ha fourier_tartarNumerator_nonneg)
    (fourier_scaledTartarNumerator_im_eq_zero a)
    (fourier_poitouGaussianCutoff_nonneg n)
    (fourier_poitouGaussianCutoff_im_eq_zero n) t

/-- Gaussian-damped numerators converge pointwise to the original numerator. -/
theorem tendsto_gaussianDampedNumerator (f : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n ↦ gaussianDampedNumerator f n x) atTop (nhds (f x)) := by
  simpa [gaussianDampedNumerator] using
    tendsto_const_nhds.mul (tendsto_poitouGaussianCutoff x)

/-- The Gaussian Poitou approximants converge pointwise to the original Poitou kernel. -/
theorem tendsto_gaussianPoitouApproximant (f : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n ↦ gaussianPoitouApproximant f n x) atTop (nhds (poitouKernel f x)) := by
  simp only [gaussianPoitouApproximant, poitouKernel_apply]
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_gaussianDampedNumerator f x).div_const (Real.cosh (x / 2)))

/-- Pointwise convergence for the correctly scaled Tartar family. -/
theorem tendsto_scaledTartar_gaussianPoitouApproximant (y x : ℝ) :
    Tendsto
      (fun n ↦ gaussianPoitouApproximant
        (scaledNumerator tartarNumerator (1 / √y)) n x)
      atTop (nhds (scaledPoitouKernel tartarNumerator (1 / √y) x)) :=
  tendsto_gaussianPoitouApproximant _ x

/-- All weak Poitou conditions for the scaled Tartar numerator except the two genuine
bounded-variation estimates. -/
theorem scaledTartar_isPoitouTestFn {y : ℝ} (hy : 0 < y)
    (hkernel_bv : BoundedVariationOn
      (poitouKernel (scaledNumerator tartarNumerator (1 / √y))) (Set.Ici 0))
    (hdiffQuot_bv : BoundedVariationOn
      (poitouDiffQuot (scaledNumerator tartarNumerator (1 / √y))) (Set.Ici 0)) :
    IsPoitouTestFn (scaledNumerator tartarNumerator (1 / √y)) := by
  have hscale : 0 < 1 / √y := one_div_pos.mpr (Real.sqrt_pos.2 hy)
  have hcontNumerator : Continuous (scaledNumerator tartarNumerator (1 / √y)) := by
    unfold scaledNumerator
    exact continuous_tartarNumerator.comp (by fun_prop)
  have hcontKernel : Continuous
      (poitouKernel (scaledNumerator tartarNumerator (1 / √y))) := by
    unfold poitouKernel
    exact Complex.continuous_ofReal.comp
      (hcontNumerator.div (by fun_prop) fun x ↦ (Real.cosh_pos (x / 2)).ne')
  refine ⟨?_, ?_, ?_, ?_, hkernel_bv, hdiffQuot_bv, ?_, ?_⟩
  · intro x
    simp only [scaledNumerator, neg_div]
    exact tartarNumerator_even _
  · simp [scaledNumerator]
  · intro x
    exact tartarNumerator_nonneg _
  · exact ((integrable_comp_div_iff tartarNumerator hscale.ne').2
      integrable_tartarNumerator).integrableOn
  · intro x
    refine ⟨poitouKernel (scaledNumerator tartarNumerator (1 / √y)) x,
      poitouKernel (scaledNumerator tartarNumerator (1 / √y)) x, ?_, ?_, by ring⟩
    · exact hcontKernel.continuousAt.mono_left inf_le_left
    · exact hcontKernel.continuousAt.mono_left inf_le_left
  · exact fourier_scaledNumerator_nonneg tartarNumerator hscale
      fourier_tartarNumerator_nonneg

end Odlyzko
