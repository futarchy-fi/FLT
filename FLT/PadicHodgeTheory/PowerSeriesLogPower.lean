/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PowerSeries.Log

/-! # Formal logarithms of products and integer powers -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The formal logarithmic derivative identity for series with constant term one. -/
theorem powerSeriesLogOf_derivative_mul {f : PowerSeries R} (hf : constantCoeff f = 1) :
    derivative (logOf f) * f = derivative f := by
  have hs : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  have h := congrArg (substAlgHom hs) (derivative_log_mul_one_add_X (A := R))
  simp only [map_mul, map_add, map_one, substAlgHom_X] at h
  have hi : (derivative (log R)).subst (f - 1) * f = 1 := by
    simpa only [coe_substAlgHom, add_sub_cancel] using h
  rw [logOf_eq, derivative_subst hs, map_sub, derivative_one, sub_zero]
  calc
    (derivative (log R)).subst (f - 1) * derivative f * f =
        ((derivative (log R)).subst (f - 1) * f) * derivative f := by ring
    _ = derivative f := by rw [hi, one_mul]

/-- Formal logarithms add on multiplication in 1 + X R[[X]]. -/
theorem powerSeriesLogOf_mul {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  let : IsAddTorsionFree R := IsAddTorsionFree.of_module_rat R
  have hfg : constantCoeff (f * g) = 1 := by simp [hf, hg]
  apply derivative.ext
  · apply (isUnit_iff_constantCoeff.mpr (show IsUnit (constantCoeff (f * g)) by
      rw [hfg]; exact isUnit_one)).mul_right_cancel
    rw [powerSeriesLogOf_derivative_mul hfg, map_add]
    have h₁ := powerSeriesLogOf_derivative_mul hf
    have h₂ := powerSeriesLogOf_derivative_mul hg
    simp only [Derivation.leibniz, smul_eq_mul]
    rw [mul_comm g (derivative f), add_comm (f * derivative g)]
    calc
      derivative f * g + f * derivative g =
          (derivative (logOf f) * f) * g + f * (derivative (logOf g) * g) := by
            rw [h₁, h₂]
      _ = (derivative (logOf f) + derivative (logOf g)) * (f * g) := by ring
  · simp only [map_add, constantCoeff_logOf hfg, constantCoeff_logOf hf,
      constantCoeff_logOf hg, add_zero]

/-- Integer powers multiply the formal logarithm by that integer. -/
theorem powerSeriesLogOf_pow {f : PowerSeries R} (hf : constantCoeff f = 1) (n : ℕ) :
    logOf (f ^ n) = n • logOf f := by
  induction n with
  | zero => simp [logOf_eq, subst_zero_of_constantCoeff_zero]
  | succ n ih =>
    rw [pow_succ, powerSeriesLogOf_mul (by simp [hf]) hf, ih, succ_nsmul]

end PadicHodgeTheory
