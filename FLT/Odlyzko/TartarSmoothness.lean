/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouGaussianRegularization
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Smoothness of the Tartar regularization

Compact support of Tartar's autocorrelation makes all of its moments integrable.  Fourier
differentiation therefore gives smoothness of every order for the normalized numerator.  This is
the regularity input needed for the bounded-variation estimates in the Gaussian regularization.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace Odlyzko

/-- Every absolute moment of Tartar's compactly supported autocorrelation is integrable. -/
theorem integrable_norm_pow_mul_norm_autocorrelation_tartarV (n : ℕ) :
    Integrable (fun x : ℝ ↦ ‖x‖ ^ n * ‖autocorrelation tartarV x‖) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow n).mul continuous_autocorrelation_tartarV.norm
  · exact hasCompactSupport_autocorrelation_tartarV.norm.mul_left

/-- The Fourier transform of Tartar's autocorrelation is smooth to every order. -/
theorem contDiff_fourier_autocorrelation_tartarV :
    ContDiff ℝ ∞ (𝓕 (autocorrelation tartarV)) := by
  apply Real.contDiff_fourier (N := ⊤)
  intro n _
  exact integrable_norm_pow_mul_norm_autocorrelation_tartarV n

/-- Poitou's normalized Tartar numerator is smooth to every order. -/
theorem contDiff_tartarNumerator : ContDiff ℝ ∞ tartarNumerator := by
  unfold tartarNumerator
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp
    (contDiff_fourier_autocorrelation_tartarV.comp
      (contDiff_id.div_const (2 * Real.pi))))

/-- Scaling preserves smoothness of the Tartar numerator. -/
theorem contDiff_scaledTartarNumerator (a : ℝ) :
    ContDiff ℝ ∞ (scaledNumerator tartarNumerator a) := by
  unfold scaledNumerator
  exact contDiff_tartarNumerator.comp (contDiff_id.div_const a)

/-- Every Gaussian-damped scaled Tartar numerator is smooth to every order. -/
theorem contDiff_gaussianDamped_scaledTartarNumerator (a : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (gaussianDampedNumerator (scaledNumerator tartarNumerator a) n) := by
  unfold gaussianDampedNumerator poitouGaussianCutoff
  exact (contDiff_scaledTartarNumerator a).mul (Real.contDiff_exp.comp
    ((contDiff_id.pow 2).neg.div_const ((n : ℝ) + 1)))

/-- Every Gaussian Poitou approximant built from a scaled Tartar numerator is smooth to every
order. -/
theorem contDiff_gaussianPoitouApproximant_scaledTartar (a : ℝ) (n : ℕ) :
    ContDiff ℝ ∞
      (gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n) := by
  unfold gaussianPoitouApproximant poitouKernel
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_gaussianDamped_scaledTartarNumerator a n).div
      (Real.contDiff_cosh.comp (contDiff_id.div_const 2))
      (fun x ↦ (Real.cosh_pos (x / 2)).ne'))

private theorem deriv_zero_of_even (F : ℝ → ℂ) (hF : Differentiable ℝ F)
    (hFeven : Function.Even F) : deriv F 0 = 0 := by
  have hderiv := (hF 0).hasDerivAt
  have hderivAtNeg : HasDerivAt F (deriv F 0) (-0) := by simpa using hderiv
  have hneg : HasDerivAt (fun x : ℝ ↦ -x) (-1) 0 := hasDerivAt_neg 0
  have hderivNeg := HasDerivAt.scomp (𝕜 := ℝ) 0 hderivAtNeg hneg
  have hcomp : F ∘ Neg.neg = F := by
    funext x
    exact hFeven x
  rw [hcomp] at hderivNeg
  have hunique := hderiv.unique hderivNeg
  have hunique' : deriv F 0 = -deriv F 0 := by simpa using hunique
  exact CharZero.eq_neg_self_iff.mp hunique'

/-- The difference quotient in the strong admissibility condition is continuous for every
Gaussian-regularized scaled Tartar kernel, including at the removable singularity at zero. -/
theorem continuous_gaussianPoitouApproximant_diffQuot_scaledTartar (a : ℝ) (n : ℕ) :
    Continuous (fun x : ℝ ↦
      (gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n 0 -
        gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n x) / x) := by
  let F := gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n
  have hFdiff : Differentiable ℝ F :=
    (contDiff_gaussianPoitouApproximant_scaledTartar a n).differentiable (by simp)
  have hFeven : Function.Even F := by
    exact poitouKernel_even (gaussianDampedNumerator_even (by
      intro x
      simpa only [scaledNumerator, neg_div] using tartarNumerator_even (x / a)) n)
  have hderiv : deriv F 0 = 0 := deriv_zero_of_even F hFdiff hFeven
  have hdslope : Continuous (dslope F 0) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact continuousAt_dslope_same.2 (hFdiff 0)
    · exact (continuousAt_dslope_of_ne hx).2 hFdiff.continuous.continuousAt
  have heq : (fun x : ℝ ↦ (F 0 - F x) / x) = fun x ↦ -dslope F 0 x := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [dslope_same, hderiv]
    · rw [dslope_of_ne _ hx]
      rw [slope_def_module]
      have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      simp only [sub_zero, Algebra.smul_def]
      push_cast
      field_simp [hxc]
      rw [mul_comm]
      simp only [← mul_neg, neg_sub]
      rfl
  rw [show (fun x : ℝ ↦
      (gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n 0 -
        gaussianPoitouApproximant (scaledNumerator tartarNumerator a) n x) / x) =
      fun x ↦ (F 0 - F x) / x by rfl, heq]
  exact hdslope.neg

end Odlyzko
