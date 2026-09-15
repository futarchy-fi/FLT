/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.AINTLIB.DedekindResidue.ExplicitFormula.GammaSide
public import FLT.Odlyzko.TartarNumerator

/-!
# Plancherel normalization of the Tartar numerator

This file uses AINTLIB's `L¹ ∩ L²` compatibility theorem for the Fourier transform to compute
the integral of Poitou's normalized Tartar numerator.  Keeping this bridge separate leaves the
elementary definition and pointwise properties in `TartarNumerator` independent of the explicit
formula development.
-/

@[expose] public section

open MeasureTheory
open Complex
open scoped FourierTransform

namespace Odlyzko

private theorem integrable_complexify_tartarV : Integrable (complexify tartarV) :=
  Complex.ofRealCLM.integrable_comp integrable_tartarV

private theorem memLp_complexify_tartarV :
    MemLp (complexify tartarV) 2 (volume : Measure ℝ) :=
  memLp_tartarV.ofReal

/-- The pointwise Fourier transform of `tartarV` is real-valued. -/
theorem fourier_tartarV_conj (t : ℝ) :
    (starRingEnd ℂ) (𝓕 (complexify tartarV) t) = 𝓕 (complexify tartarV) t := by
  rw [← fourier_reflect_eq_conj]
  apply Real.fourier_congr_ae
  filter_upwards with x
  simp only [complexify, reflect]
  exact congrArg Complex.ofReal (tartarV_even x)

/-- The pointwise transform of `tartarV` represents an `L²` function. -/
theorem memLp_fourier_tartarV :
    MemLp (𝓕 (complexify tartarV)) 2 (volume : Measure ℝ) := by
  exact (MeasureTheory.Lp.memLp _).ae_eq
    (DedekindResidue.coeFn_fourier_toLp_two integrable_complexify_tartarV
      memLp_complexify_tartarV)

/-- The squared norm of the Fourier transform is integrable. -/
theorem integrable_norm_sq_fourier_tartarV :
    Integrable (fun t : ℝ ↦ ‖𝓕 (complexify tartarV) t‖ ^ 2) :=
  memLp_fourier_tartarV.integrable_norm_pow (p := 2) (by norm_num)

/-- Plancherel's identity for the concrete Tartar profile. -/
theorem integral_norm_sq_fourier_tartarV :
    ∫ t : ℝ, ‖𝓕 (complexify tartarV) t‖ ^ 2 = 16 / 15 := by
  have hpair := DedekindResidue.integral_fourier_mul_fourierL2
    integrable_complexify_tartarV memLp_complexify_tartarV memLp_complexify_tartarV
  have hbridge := DedekindResidue.coeFn_fourier_toLp_two
    integrable_complexify_tartarV memLp_complexify_tartarV
  have hcomplex : ((∫ t : ℝ, ‖𝓕 (complexify tartarV) t‖ ^ 2 : ℝ) : ℂ) =
      ((16 / 15 : ℝ) : ℂ) := calc
    ((∫ t : ℝ, ‖𝓕 (complexify tartarV) t‖ ^ 2 : ℝ) : ℂ) =
        ∫ t : ℝ, ((‖𝓕 (complexify tartarV) t‖ ^ 2 : ℝ) : ℂ) :=
      integral_ofReal.symm
    _ =
        ∫ t : ℝ, 𝓕 (complexify tartarV) t *
          ((𝓕 (memLp_complexify_tartarV.toLp (complexify tartarV)) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t := by
      refine integral_congr_ae ?_
      filter_upwards [hbridge] with t ht
      rw [ht]
      calc
        ((‖𝓕 (complexify tartarV) t‖ ^ 2 : ℝ) : ℂ) =
            𝓕 (complexify tartarV) t *
              (starRingEnd ℂ) (𝓕 (complexify tartarV) t) :=
          by
            push_cast
            exact (RCLike.mul_conj (K := ℂ) (𝓕 (complexify tartarV) t)).symm
        _ = 𝓕 (complexify tartarV) t * 𝓕 (complexify tartarV) t := by
          rw [fourier_tartarV_conj]
    _ = ∫ x : ℝ, complexify tartarV (-x) * complexify tartarV x := hpair
    _ = ((16 / 15 : ℝ) : ℂ) := by
      rw [show (fun x : ℝ ↦ complexify tartarV (-x) * complexify tartarV x) =
          fun x : ℝ ↦ ((tartarV (-x) * tartarV x : ℝ) : ℂ) by
        funext x
        simp [complexify]]
      rw [integral_complex_ofReal]
      have hzero := tartarV_autocorrelation_at_zero
      rw [realAutocorrelation, MeasureTheory.convolution_def] at hzero
      simpa [reflect] using congrArg Complex.ofReal hzero
  exact Complex.ofReal_injective hcomplex

/-- Poitou's normalized numerator is integrable. -/
theorem integrable_tartarNumerator : Integrable tartarNumerator := by
  rw [show tartarNumerator = fun x : ℝ => 9 / 16 *
      ‖𝓕 (complexify tartarV) (x / (2 * Real.pi))‖ ^ 2 by
    funext x
    exact tartarNumerator_eq_norm_sq x]
  exact ((integrable_comp_div_iff _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)).2
    integrable_norm_sq_fourier_tartarV).const_mul _

/-- The total mass of Poitou's normalized Tartar numerator is `6π/5`. -/
theorem integral_tartarNumerator :
    ∫ x : ℝ, tartarNumerator x = 6 * Real.pi / 5 := by
  simp_rw [tartarNumerator_eq_norm_sq]
  rw [integral_const_mul,
    MeasureTheory.Measure.integral_comp_div
      (g := fun t : ℝ => ‖𝓕 (complexify tartarV) t‖ ^ 2) (2 * Real.pi),
    integral_norm_sq_fourier_tartarV, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  ring

/-- The positive half of the mass is `3π/5`, as used by Poitou. -/
theorem integral_tartarNumerator_Ioi :
    ∫ x in Set.Ioi (0 : ℝ), tartarNumerator x = 3 * Real.pi / 5 := by
  have habs : (fun x : ℝ => tartarNumerator |x|) = tartarNumerator := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, tartarNumerator_even]
  have h := integral_comp_abs (f := tartarNumerator)
  rw [habs, integral_tartarNumerator] at h
  linarith

/-- Closed-endpoint form of `integral_tartarNumerator_Ioi`. -/
theorem integral_tartarNumerator_Ici :
    ∫ x in Set.Ici (0 : ℝ), tartarNumerator x = 3 * Real.pi / 5 := by
  rw [integral_Ici_eq_integral_Ioi]
  exact integral_tartarNumerator_Ioi

private theorem integrable_autocorrelation_tartarV : Integrable (autocorrelation tartarV) :=
  continuous_autocorrelation_tartarV.integrable_of_hasCompactSupport
    hasCompactSupport_autocorrelation_tartarV

private theorem integrable_fourier_autocorrelation_tartarV :
    Integrable (𝓕 (autocorrelation tartarV)) := by
  refine integrable_norm_sq_fourier_tartarV.ofReal.congr ?_
  filter_upwards with t
  rw [fourier_autocorrelation_tartarV]
  norm_cast

/-- Applying the Fourier transform twice to Tartar's even autocorrelation returns it. -/
theorem fourier_fourier_autocorrelation_tartarV (t : ℝ) :
    𝓕 (𝓕 (autocorrelation tartarV)) t = autocorrelation tartarV t := by
  have hinv := continuous_autocorrelation_tartarV.fourierInv_fourier_eq
    integrable_autocorrelation_tartarV integrable_fourier_autocorrelation_tartarV
  have hneg := congrFun hinv (-t)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at hneg
  rw [hneg]
  exact autocorrelation_tartarV_even t

/-- Complex form of the numerator as a scaled Fourier transform of the autocorrelation. -/
theorem complexify_tartarNumerator :
    complexify tartarNumerator =
      (9 / 16 : ℂ) • scaled (𝓕 (autocorrelation tartarV)) (2 * Real.pi) := by
  funext x
  rw [Pi.smul_apply]
  simp only [complexify, scaled]
  rw [tartarNumerator_eq_norm_sq, fourier_autocorrelation_tartarV]
  norm_num

/-- The Fourier transform of the normalized numerator is a positive multiple of Tartar's
autocorrelation. -/
theorem fourier_tartarNumerator (t : ℝ) :
    𝓕 (complexify tartarNumerator) t =
      (9 * Real.pi / 8 : ℂ) * autocorrelation tartarV (2 * Real.pi * t) := by
  rw [complexify_tartarNumerator]
  change 𝓕 (fun x : ℝ => (9 / 16 : ℂ) *
    scaled (𝓕 (autocorrelation tartarV)) (2 * Real.pi) x) t = _
  calc
    _ = (9 / 16 : ℂ) * 𝓕 (scaled (𝓕 (autocorrelation tartarV))
        (2 * Real.pi)) t := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      simp only [Circle.smul_def]
      ring
    _ = _ := by
      rw [fourier_scaled _ (by positivity : 0 < 2 * Real.pi),
        fourier_fourier_autocorrelation_tartarV]
      push_cast
      ring

/-- Fourier positivity of Poitou's normalized Tartar numerator. -/
theorem fourier_tartarNumerator_nonneg (t : ℝ) :
    0 ≤ (𝓕 (complexify tartarNumerator) t).re := by
  rw [fourier_tartarNumerator]
  rw [show (9 * (Real.pi : ℂ) / 8) = ((9 * Real.pi / 8 : ℝ) : ℂ) by
    push_cast
    rfl]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg
  · positivity
  · rw [autocorrelation_eq_ofReal_realAutocorrelation]
    simp only [ofReal_re]
    exact realAutocorrelation_tartarV_nonneg _

end Odlyzko
