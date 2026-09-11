/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouKernel

/-!
# Scaling Odlyzko test functions

The generic helper `scaled F y` uses the convention `F(x / y)`.  In the unconditional
Poitou family it is the real numerator `f`, not the explicit-formula kernel, that is
scaled.  The resulting kernel is `poitouKernel (scaledNumerator f y)`.

The elementary structural properties are recorded here.  Preserving the full
`IsAdmissibleTestFn` predicate for every positive scale needs the compact-support
and regularity data of the concrete autocorrelation package; it does not follow
from abstract admissibility alone.
-/

@[expose] public section

open scoped FourierTransform
open MeasureTheory

namespace Odlyzko

/-- Generic scaling by division in the argument. -/
noncomputable def scaled (F : ℝ → ℂ) (y : ℝ) : ℝ → ℂ := fun x ↦ F (x / y)

/-- The real numerator scaled before the Poitou kernel is formed. -/
noncomputable def scaledNumerator (f : ℝ → ℝ) (y : ℝ) : ℝ → ℝ := fun x ↦ f (x / y)

/-- The unconditional scaled kernel: scale `f` first, then divide by `cosh(x / 2)`. -/
noncomputable def scaledPoitouKernel (f : ℝ → ℝ) (y : ℝ) : ℝ → ℂ :=
  poitouKernel (scaledNumerator f y)

@[simp] theorem scaledPoitouKernel_apply (f : ℝ → ℝ) (y x : ℝ) :
    scaledPoitouKernel f y x = ((f (x / y) / Real.cosh (x / 2) : ℝ) : ℂ) := rfl

theorem complexify_scaledNumerator (f : ℝ → ℝ) (y : ℝ) :
    complexify (scaledNumerator f y) = scaled (complexify f) y := rfl

/-- Fourier transform of `F_y(x) = F(x / y)` for a positive scale. -/
theorem fourier_scaled (F : ℝ → ℂ) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    𝓕 (scaled F y) t = (y : ℂ) * 𝓕 F (y * t) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  change (∫ v : ℝ, Real.fourierChar (-(v * t)) • F (v / y)) =
    (y : ℂ) * ∫ v : ℝ, Real.fourierChar (-(v * (y * t))) • F v
  have hfun : (fun v : ℝ ↦ Real.fourierChar (-(v * t)) • F (v / y)) =
      fun v : ℝ ↦
        (fun u : ℝ ↦ Real.fourierChar (-(u * (y * t))) • F u) (v / y) := by
    funext v
    congr 2
    field_simp
  rw [hfun]
  calc
    _ = |y| • ∫ v : ℝ, Real.fourierChar (-(v * (y * t))) • F v :=
      MeasureTheory.Measure.integral_comp_div
        (fun u : ℝ ↦ Real.fourierChar (-(u * (y * t))) • F u) y
    _ = _ := by rw [abs_of_pos hy]; rfl

/-- Pointwise nonnegativity is preserved by positive scaling. -/
theorem scaled_nonneg (F : ℝ → ℂ) {y : ℝ}
    (hF : ∀ x, 0 ≤ (F x).re) (x : ℝ) :
    0 ≤ (scaled F y x).re :=
  hF (x / y)

/-- Fourier nonnegativity is preserved by positive scaling. -/
theorem fourier_scaled_nonneg (F : ℝ → ℂ) {y : ℝ} (hy : 0 < y)
    (hF : ∀ t, 0 ≤ (𝓕 F t).re) (t : ℝ) :
    0 ≤ (𝓕 (scaled F y) t).re := by
  rw [fourier_scaled F hy t]
  simpa using mul_nonneg hy.le (hF (y * t))

/-- Fourier positivity is preserved on the numerator of the scaled Poitou family. -/
theorem fourier_scaledNumerator_nonneg (f : ℝ → ℝ) {y : ℝ} (hy : 0 < y)
    (hf : ∀ t, 0 ≤ (𝓕 (complexify f) t).re) (t : ℝ) :
    0 ≤ (𝓕 (complexify (scaledNumerator f y)) t).re := by
  rw [complexify_scaledNumerator]
  exact fourier_scaled_nonneg (complexify f) hy hf t

/-- Evenness is preserved by scaling. -/
theorem scaled_even (F : ℝ → ℂ) (y : ℝ) (hF : Function.Even F) :
    Function.Even (scaled F y) := by
  intro x
  simpa only [scaled, neg_div] using hF (x / y)

/-- Compact support is preserved by a nonzero scale. -/
theorem scaled_hasCompactSupport (F : ℝ → ℂ) {y : ℝ} (hy : y ≠ 0)
    (hF : HasCompactSupport F) : HasCompactSupport (scaled F y) := by
  change HasCompactSupport (fun x ↦ F (x / y))
  simpa [scaled, div_eq_mul_inv, mul_comm] using hF.comp_smul (inv_ne_zero hy)

/-- Continuity is preserved by a nonzero scale. -/
theorem continuous_scaled (F : ℝ → ℂ) (y : ℝ) (hF : Continuous F) :
    Continuous (scaled F y) := by
  exact hF.comp (by fun_prop)

end Odlyzko
