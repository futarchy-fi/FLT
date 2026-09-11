/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.AutocorrelationNonnegative

/-!
# The unconditional Poitou kernel

The unconditional discriminant argument uses two different functions.  Its nonnegative
Fourier transform belongs to the numerator `f`; the explicit-formula kernel is
`F(x) = f(x) / cosh(x / 2)`.  Keeping those names separate prevents the invalid inference
that Fourier positivity of `F` alone controls the whole critical strip.
-/

@[expose] public section

open scoped FourierTransform

namespace Odlyzko

/-- The explicit-formula kernel in Poitou's unconditional argument. -/
noncomputable def poitouKernel (f : ℝ → ℝ) : ℝ → ℂ :=
  fun x ↦ ((f x / Real.cosh (x / 2) : ℝ) : ℂ)

@[simp] theorem poitouKernel_apply (f : ℝ → ℝ) (x : ℝ) :
    poitouKernel f x = ((f x / Real.cosh (x / 2) : ℝ) : ℂ) := rfl

/-- Even numerators give even Poitou kernels. -/
theorem poitouKernel_even {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (poitouKernel f) := by
  intro x
  simp only [poitouKernel_apply, neg_div]
  norm_cast
  rw [hf x, Real.cosh_neg]

/-- Pointwise nonnegativity passes from the numerator to the Poitou kernel. -/
theorem poitouKernel_re_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ (poitouKernel f x).re := by
  simp only [poitouKernel_apply, Complex.ofReal_re]
  exact div_nonneg (hf x) (Real.cosh_pos _).le

/-- Multiplication by `cosh(x / 2)` recovers the numerator exactly. -/
theorem poitouKernel_mul_cosh (f : ℝ → ℝ) (x : ℝ) :
    poitouKernel f x * Real.cosh (x / 2) = f x := by
  rw [poitouKernel_apply]
  norm_cast
  exact div_mul_cancel₀ _ (Real.cosh_pos (x / 2)).ne'

/-- Frequency matching Mathlib's `exp (-2 * pi * i * x * xi)` Fourier convention. -/
noncomputable def poitouFourierFrequency (γ : ℝ) : ℝ := -γ / (2 * Real.pi)

/--
The exact boundary contract for the transform attached to `F = f / cosh(x / 2)`.

The integral identity belongs at the explicit-formula seam, where `phi` will eventually be
defined.  This structure records its correctly normalized conclusion without identifying
`phi (1/2 + iγ)` with the Fourier transform at the wrong frequency.
-/
structure PoitouBoundaryIdentification (phi : ℂ → ℂ) (f : ℝ → ℝ) : Prop where
  lower : ∀ γ : ℝ,
    (phi (γ * Complex.I)).re =
      (𝓕 (complexify f) (poitouFourierFrequency γ)).re
  upper : ∀ γ : ℝ,
    (phi (1 + γ * Complex.I)).re =
      (𝓕 (complexify f) (poitouFourierFrequency γ)).re

/-- Fourier positivity of `f` gives positivity on the lower boundary. -/
theorem PoitouBoundaryIdentification.lower_nonneg
    {phi : ℂ → ℂ} {f : ℝ → ℝ} (h : PoitouBoundaryIdentification phi f)
    (hfourier : ∀ t, 0 ≤ (𝓕 (complexify f) t).re) (γ : ℝ) :
    0 ≤ (phi (γ * Complex.I)).re := by
  rw [h.lower]
  exact hfourier _

/-- Fourier positivity of `f` gives positivity on the upper boundary. -/
theorem PoitouBoundaryIdentification.upper_nonneg
    {phi : ℂ → ℂ} {f : ℝ → ℝ} (h : PoitouBoundaryIdentification phi f)
    (hfourier : ∀ t, 0 ≤ (𝓕 (complexify f) t).re) (γ : ℝ) :
    0 ≤ (phi (1 + γ * Complex.I)).re := by
  rw [h.upper]
  exact hfourier _

/-- The real autocorrelation from Q1 supplies Fourier positivity for a Poitou numerator. -/
theorem fourier_realAutocorrelation_nonneg (g : ℝ → ℝ)
    (hg : MeasureTheory.Integrable g) (t : ℝ) :
    0 ≤ (𝓕 (complexify (realAutocorrelation g)) t).re := by
  have hfunctions : complexify (realAutocorrelation g) = autocorrelation g := by
    funext x
    exact (autocorrelation_eq_ofReal_realAutocorrelation g x).symm
  rw [hfunctions]
  exact fourier_autocorrelation_nonneg g hg t

end Odlyzko
