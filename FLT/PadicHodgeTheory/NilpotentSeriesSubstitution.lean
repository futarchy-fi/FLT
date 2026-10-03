/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.NilpotentSeriesEvaluation
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Log

/-! # Nilpotent evaluation commutes with formal substitution -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R] {x : R}

/-- Substitution by a nilpotent constant gives the constant evaluation series. -/
theorem nilpotentSeries_subst_constant (hx : IsNilpotent x) (f : PowerSeries R) :
    f.subst (C x) = C (nilpotentSeriesEval hx f) := by
  let : IsAddTorsionFree R := IsAddTorsionFree.of_module_rat R
  apply derivative.ext
  · rw [derivative_subst (nilpotentConstant_hasSubst hx), derivative_C,
      mul_zero, derivative_C]
  · rw [constantCoeff_C]
    rw [nilpotentSeriesEval_apply]

omit [Algebra ℚ R] in
/-- Zero-constant series take nilpotent values at nilpotent inputs. -/
theorem nilpotentSeriesEval_isNilpotent (hx : IsNilpotent x) {g : PowerSeries R}
    (hg : constantCoeff g = 0) : IsNilpotent (nilpotentSeriesEval hx g) := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.mpr hg
  rw [map_mul, nilpotentSeriesEval_X]
  exact (Commute.all _ _).isNilpotent_mul_right hx

/-- Evaluation commutes with substitution of a series with zero constant coefficient. -/
theorem nilpotentSeriesEval_subst (hx : IsNilpotent x) {g : PowerSeries R}
    (hg : constantCoeff g = 0) (f : PowerSeries R) :
    nilpotentSeriesEval hx (f.subst g) =
      nilpotentSeriesEval (nilpotentSeriesEval_isNilpotent hx hg) f := by
  have h := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg)
    (nilpotentConstant_hasSubst hx) f
  rw [nilpotentSeries_subst_constant hx g] at h
  have hc := congrArg constantCoeff h
  simpa only [nilpotentSeriesEval_apply] using hc

end PadicHodgeTheory
