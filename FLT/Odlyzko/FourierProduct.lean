/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform of a product

An `L¹` product has transform equal to the convolution of the transforms when both factors and
their transforms satisfy Fourier inversion.  This is the form needed to transfer Fourier
positivity through Gaussian damping in the Poitou construction.
-/

@[expose] public section

open MeasureTheory
open scoped Convolution FourierTransform

namespace Odlyzko

/-- For even `L¹` functions covered by inversion, the Fourier transform of their product is the
convolution of their Fourier transforms.  Compact support of the first transform is a convenient
minimal hypothesis ensuring continuity of that convolution. -/
theorem fourier_mul_eq_convolution_of_even (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g)
    (hF : Integrable (𝓕 f)) (hG : Integrable (𝓕 g))
    (hfg : Integrable (fun x ↦ f x * g x))
    (hfcont : Continuous f) (hgcont : Continuous g)
    (hfeven : Function.Even f) (hgeven : Function.Even g)
    (hFcompact : HasCompactSupport (𝓕 f)) :
    𝓕 (fun x ↦ f x * g x) =
      (𝓕 f) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕 g) := by
  have hFcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hHcont : Continuous ((𝓕 f) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕 g)) :=
    hFcompact.continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
      hFcont hG.locallyIntegrable
  have hHint : Integrable ((𝓕 f) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕 g)) :=
    hF.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hG
  have hff (x : ℝ) : 𝓕 (𝓕 f) x = f x := by
    have h := congrFun (hfcont.fourierInv_fourier_eq hf hF) (-x)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
    exact h.trans (hfeven x)
  have hgg (x : ℝ) : 𝓕 (𝓕 g) x = g x := by
    have h := congrFun (hgcont.fourierInv_fourier_eq hg hG) (-x)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
    exact h.trans (hgeven x)
  have hfourierH :
      𝓕 ((𝓕 f) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕 g)) = fun x ↦ f x * g x := by
    funext x
    rw [Real.fourier_mul_convolution_eq hF hG, hff, hgg]
  have hfourierHint :
      Integrable (𝓕 ((𝓕 f) ⋆[ContinuousLinearMap.mul ℂ ℂ] (𝓕 g))) := by
    rw [hfourierH]
    exact hfg
  have hinv := hHcont.fourierInv_fourier_eq hHint hfourierHint
  rw [hfourierH] at hinv
  have hevenProduct : (fun x : ℝ ↦ f (-x) * g (-x)) = fun x ↦ f x * g x := by
    funext x
    rw [hfeven, hgeven]
  have hinvProduct := Real.fourierInv_eq_fourier_comp_neg (fun x ↦ f x * g x)
  rw [hevenProduct] at hinvProduct
  rw [← hinvProduct, hinv]

/-- A convolution of pointwise nonnegative real-valued complex functions has nonnegative real
part.  Compact support and continuity of the first factor ensure that the convolution exists at
every point, rather than merely almost everywhere. -/
theorem convolution_re_nonneg_of_nonneg (f g : ℝ → ℂ)
    (hfcompact : HasCompactSupport f) (hfcont : Continuous f)
    (hg : LocallyIntegrable g)
    (hfre : ∀ x, 0 ≤ (f x).re) (hfim : ∀ x, (f x).im = 0)
    (hgre : ∀ x, 0 ≤ (g x).re) (hgim : ∀ x, (g x).im = 0) (t : ℝ) :
    0 ≤ ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) t).re := by
  have hconv := hfcompact.convolutionExists_left (ContinuousLinearMap.mul ℂ ℂ)
    hfcont hg t
  change Integrable (fun x ↦ (ContinuousLinearMap.mul ℂ ℂ (f x)) (g (t - x))) at hconv
  rw [MeasureTheory.convolution_def]
  calc
    0 ≤ ∫ x : ℝ, ((ContinuousLinearMap.mul ℂ ℂ (f x)) (g (t - x))).re := by
      apply integral_nonneg
      intro x
      change 0 ≤ (f x * g (t - x)).re
      rw [Complex.mul_re, hfim, hgim, zero_mul, sub_zero]
      exact mul_nonneg (hfre x) (hgre (t - x))
    _ = (∫ x : ℝ, (ContinuousLinearMap.mul ℂ ℂ (f x)) (g (t - x))).re :=
      integral_re hconv

end Odlyzko
