/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Scaling
public import FLT.Odlyzko.Tartar

/-!
# The normalized Tartar numerator

Poitou's numerical test function is the normalized Fourier transform of
`w = tartarV ⋆ tartarV`, not `w` itself.  With Mathlib's `2π` Fourier convention it is

`f(x) = (9/16) Re(𝓕w(x/(2π))) = (9/16) ‖𝓕v(x/(2π))‖²`.

This file records the definition, positivity, and the normalization `f(0)=1`.
-/

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace Odlyzko

/-- Poitou's normalized Tartar numerator in Mathlib's Fourier convention. -/
noncomputable def tartarNumerator (x : ℝ) : ℝ :=
  9 / 16 * (𝓕 (autocorrelation tartarV) (x / (2 * Real.pi))).re

/-- The numerator is the normalized squared norm of the transform of `tartarV`. -/
theorem tartarNumerator_eq_norm_sq (x : ℝ) :
    tartarNumerator x = 9 / 16 * ‖𝓕 (complexify tartarV) (x / (2 * Real.pi))‖ ^ 2 := by
  rw [tartarNumerator, fourier_autocorrelation_tartarV]
  norm_num [pow_two, Complex.mul_re]

/-- The normalized Tartar numerator is pointwise nonnegative. -/
theorem tartarNumerator_nonneg (x : ℝ) : 0 ≤ tartarNumerator x := by
  rw [tartarNumerator_eq_norm_sq]
  positivity

/-- The normalized Tartar numerator is even. -/
theorem tartarNumerator_even : Function.Even tartarNumerator := by
  have h := Real.fourierInv_eq_fourier_comp_neg (complexify tartarV)
  have heven : (fun t : ℝ ↦ complexify tartarV (-t)) = complexify tartarV := by
    funext t
    simp only [complexify]
    exact congrArg Complex.ofReal (tartarV_even t)
  rw [heven] at h
  have hFourier : Function.Even (𝓕 (complexify tartarV)) := by
    intro t
    rw [← Real.fourierInv_eq_fourier_neg]
    exact congrFun h t
  intro x
  rw [tartarNumerator_eq_norm_sq, tartarNumerator_eq_norm_sq]
  simpa only [neg_div] using congrArg (fun z : ℂ ↦ 9 / 16 * ‖z‖ ^ 2)
    (hFourier (x / (2 * Real.pi)))

/-- The normalized Tartar numerator is continuous. -/
theorem continuous_tartarNumerator : Continuous tartarNumerator := by
  have hFourier : Continuous (𝓕 (autocorrelation tartarV)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂
      (continuous_autocorrelation_tartarV.integrable_of_hasCompactSupport
        hasCompactSupport_autocorrelation_tartarV)
  unfold tartarNumerator
  fun_prop

/-- The integral of `tartarV` is `4/3`. -/
theorem integral_tartarV : ∫ t : ℝ, tartarV t = 4 / 3 := by
  have hzero : ∀ t : ℝ, t ∉ Set.Icc (-1) 1 → tartarV t = 0 := by
    intro t ht
    exact Function.notMem_support.mp fun h ↦ ht (support_tartarV_subset h)
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hIcc : ∫ t in Set.Icc (-1 : ℝ) 1, tartarV t =
      ∫ t in Set.Icc (-1 : ℝ) 1, (1 - t ^ 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    rw [tartarV_apply, max_eq_left]
    nlinarith [ht.1, ht.2]
  rw [hIcc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hderiv : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x : ℝ ↦ x - x ^ 3 / 3) (1 - t ^ 2) t := by
    intro t _
    have d3 := hasDerivAt_pow 3 t
    have d1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id' (x := t)
    refine HasDerivAt.congr_deriv (d1.sub (d3.div_const 3)) ?_
    norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.sub (continuous_pow 2)).intervalIntegrable _ _)]
  norm_num

/-- The Fourier transform of `tartarV` at zero is its integral, hence `4/3`. -/
theorem fourier_tartarV_zero : 𝓕 (complexify tartarV) 0 = 4 / 3 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, complexify]
  calc
    (∫ v : ℝ, (tartarV v : ℂ)) = (∫ v : ℝ, tartarV v) :=
      integral_complex_ofReal
    _ = 4 / 3 := by rw [integral_tartarV]; norm_num

/-- Poitou's normalization: the Tartar numerator takes the value one at the origin. -/
@[simp] theorem tartarNumerator_zero : tartarNumerator 0 = 1 := by
  rw [tartarNumerator_eq_norm_sq, zero_div, fourier_tartarV_zero]
  norm_num

/-- Poitou's parameter `y` corresponds to scale `1 / sqrt y` in `scaledNumerator`. -/
theorem scaledNumerator_tartar_eq (y x : ℝ) (hy : 0 < y) :
    scaledNumerator tartarNumerator (1 / √y) x = tartarNumerator (x * √y) := by
  rw [scaledNumerator]
  congr 1
  field_simp [Real.sqrt_ne_zero'.2 hy]

/-- The scaled Poitou kernel has the argument convention used in Poitou's series. -/
theorem scaledPoitouKernel_tartar_eq (y x : ℝ) (hy : 0 < y) :
    scaledPoitouKernel tartarNumerator (1 / √y) x =
      ((tartarNumerator (x * √y) / Real.cosh (x / 2) : ℝ) : ℂ) := by
  rw [scaledPoitouKernel_apply]
  change ((scaledNumerator tartarNumerator (1 / √y) x /
    Real.cosh (x / 2) : ℝ) : ℂ) = _
  rw [scaledNumerator_tartar_eq y x hy]

end Odlyzko
