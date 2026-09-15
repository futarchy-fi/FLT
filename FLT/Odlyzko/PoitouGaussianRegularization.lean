/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouRegularization
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
  rw [hfun, fourier_gaussian_innerProductSpace (V := ℝ) (by simpa using hb)]
  simp only [Module.finrank_self, Nat.cast_one]
  rw [show ((Real.pi : ℂ) / (b : ℂ)) = ((Real.pi / b : ℝ) : ℂ) by push_cast; rfl,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / b) (1 / 2)]
  rw [show (-(Real.pi : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / (b : ℂ)) =
      ((-Real.pi ^ 2 * ‖t‖ ^ 2 / b : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_re,
    Complex.exp_ofReal_im, mul_zero, sub_zero]
  positivity

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
