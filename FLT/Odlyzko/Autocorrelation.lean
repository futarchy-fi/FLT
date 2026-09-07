/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Analysis.Fourier.Convolution

/-!
# Autocorrelation test functions

This file isolates the structural facts behind the Odlyzko test function.  The input is
kept abstract: the later Tartar-function packet only has to provide a concrete `g`.
-/

@[expose] public section

open scoped ComplexConjugate Convolution FourierTransform Pointwise
open MeasureTheory

namespace Odlyzko

/-- A real function viewed as complex-valued. -/
def complexify (g : ℝ → ℝ) : ℝ → ℂ := fun x ↦ g x

/-- Reflection in the origin. -/
def reflect (g : ℝ → ℝ) : ℝ → ℝ := fun x ↦ g (-x)

/-- The autocorrelation used in the Odlyzko construction. -/
noncomputable def autocorrelation (g : ℝ → ℝ) : ℝ → ℂ :=
  complexify g ⋆[ContinuousLinearMap.mul ℂ ℂ] complexify (reflect g)

private theorem integrable_complexify {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (complexify g) := by
  exact Complex.ofRealCLM.integrable_comp hg

private theorem integrable_reflect {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (complexify (reflect g)) := by
  exact Complex.ofRealCLM.integrable_comp (by simpa [reflect] using hg.comp_neg)

/-- The Fourier transform of a reflected real function is the conjugate transform. -/
theorem fourier_reflect_eq_conj (g : ℝ → ℝ) (t : ℝ) :
    𝓕 (complexify (reflect g)) t = conj (𝓕 (complexify g) t) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  rw [← integral_conj]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with x
  simp only [complexify, reflect, Circle.smul_def, Real.fourierChar_apply, neg_mul, neg_neg]
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  congr 1
  simp

/-- Fourier transform of an autocorrelation: `F̂ = |ĝ|²`. -/
theorem fourier_autocorrelation (g : ℝ → ℝ) (hg : Integrable g) (t : ℝ) :
    𝓕 (autocorrelation g) t = ‖𝓕 (complexify g) t‖ ^ 2 := by
  rw [autocorrelation, Real.fourier_mul_convolution_eq
    (integrable_complexify hg) (integrable_reflect hg), fourier_reflect_eq_conj g]
  exact RCLike.mul_conj _

/-- Fourier positivity is automatic for the autocorrelation construction. -/
theorem fourier_autocorrelation_nonneg (g : ℝ → ℝ) (hg : Integrable g) (t : ℝ) :
    0 ≤ (𝓕 (autocorrelation g) t).re := by
  rw [fourier_autocorrelation g hg t]
  norm_cast
  exact sq_nonneg _

/-- An even input has an even autocorrelation. -/
theorem autocorrelation_even (g : ℝ → ℝ) (hg : Function.Even g) :
    Function.Even (autocorrelation g) := by
  intro x
  apply MeasureTheory.convolution_neg_of_neg_eq
  · exact Filter.Eventually.of_forall fun y ↦ by simp [complexify, hg y]
  · exact Filter.Eventually.of_forall fun y ↦ by simp [complexify, reflect, hg y]

/-- Compact support is preserved by autocorrelation. -/
theorem autocorrelation_hasCompactSupport (g : ℝ → ℝ) (hg : HasCompactSupport g) :
    HasCompactSupport (autocorrelation g) := by
  apply HasCompactSupport.convolution
  · exact hg.comp_left rfl
  · exact (hg.comp_homeomorph (Homeomorph.neg ℝ)).comp_left rfl

/-- The support of the autocorrelation lies in the sum of the input support and its reflection. -/
theorem support_autocorrelation_subset (g : ℝ → ℝ) :
    Function.support (autocorrelation g) ⊆
      Function.support (complexify g) + Function.support (complexify (reflect g)) := by
  exact MeasureTheory.support_convolution_subset _

/-- A continuous compactly supported input has a continuous autocorrelation. -/
theorem continuous_autocorrelation (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Continuous (autocorrelation g) := by
  apply HasCompactSupport.continuous_convolution_right
  · exact (hgc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left rfl
  · exact (integrable_complexify (hg.integrable_of_hasCompactSupport hgc)).locallyIntegrable
  · exact Complex.continuous_ofReal.comp (hg.comp continuous_neg)

/-- The Q1 package, with the `L²` hypothesis recorded for its later analytic consumers. -/
theorem autocorrelation_structural_package (g : ℝ → ℝ)
    (hg_even : Function.Even g) (hg_cont : Continuous g) (hg_compact : HasCompactSupport g)
    (_hg_L2 : MemLp g 2 volume) :
    Function.Even (autocorrelation g) ∧
      HasCompactSupport (autocorrelation g) ∧
      Continuous (autocorrelation g) ∧
      ∀ t, 𝓕 (autocorrelation g) t = ‖𝓕 (complexify g) t‖ ^ 2 ∧
        0 ≤ (𝓕 (autocorrelation g) t).re := by
  have hg_int : Integrable g := hg_cont.integrable_of_hasCompactSupport hg_compact
  exact ⟨autocorrelation_even g hg_even, autocorrelation_hasCompactSupport g hg_compact,
    continuous_autocorrelation g hg_cont hg_compact, fun t ↦
      ⟨fourier_autocorrelation g hg_int t, fourier_autocorrelation_nonneg g hg_int t⟩⟩

end Odlyzko
