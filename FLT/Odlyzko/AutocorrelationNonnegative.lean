/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Autocorrelation

/-!
# Pointwise positivity of an abstract autocorrelation

Autocorrelation alone gives Fourier positivity, not positivity in the original variable.  A simple
sufficient condition is that the abstract input itself be nonnegative.  Whether Poitou's concrete
Tartar function satisfies this condition is deliberately left to the later instantiation packet.
-/

@[expose] public section

open scoped Convolution FourierTransform
open MeasureTheory

namespace Odlyzko

/-- The real-valued form of the autocorrelation. -/
noncomputable def realAutocorrelation (g : ℝ → ℝ) : ℝ → ℝ :=
  g ⋆[ContinuousLinearMap.lsmul ℝ ℝ] reflect g

/-- The complex autocorrelation from Q1 is the complexification of the real one. -/
theorem autocorrelation_eq_ofReal_realAutocorrelation (g : ℝ → ℝ) (x : ℝ) :
    autocorrelation g x = realAutocorrelation g x := by
  rw [autocorrelation, realAutocorrelation, MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  rw [← integral_complex_ofReal]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp [complexify, reflect]

/-- A pointwise nonnegative input has a pointwise nonnegative real autocorrelation. -/
theorem realAutocorrelation_nonneg (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (x : ℝ) :
    0 ≤ realAutocorrelation g x := by
  rw [realAutocorrelation, MeasureTheory.convolution_def]
  apply MeasureTheory.integral_nonneg
  intro t
  exact mul_nonneg (hg t) (hg (-(x - t)))

/-- Pointwise positivity for the same complex-valued autocorrelation used in Q1. -/
theorem autocorrelation_re_nonneg_of_nonneg (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (x : ℝ) :
    0 ≤ (autocorrelation g x).re := by
  rw [autocorrelation_eq_ofReal_realAutocorrelation]
  exact realAutocorrelation_nonneg g hg x

/-- The abstract sufficient-condition package: `F ≥ 0` and `F̂ ≥ 0` simultaneously. -/
theorem autocorrelation_and_fourier_nonneg (g : ℝ → ℝ) (hg_integrable : Integrable g)
    (hg_nonneg : ∀ x, 0 ≤ g x) :
    (∀ x, 0 ≤ (autocorrelation g x).re) ∧
      ∀ t, 0 ≤ (𝓕 (autocorrelation g) t).re :=
  ⟨autocorrelation_re_nonneg_of_nonneg g hg_nonneg,
    fourier_autocorrelation_nonneg g hg_integrable⟩

end Odlyzko
