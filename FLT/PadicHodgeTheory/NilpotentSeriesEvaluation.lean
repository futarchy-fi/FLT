/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Algebraic evaluation of formal series at nilpotent elements -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open PowerSeries
variable {R : Type*} [CommRing R] {x : R}

/-- A nilpotent constant is a valid formal substitution, without a topology on R. -/
theorem nilpotentConstant_hasSubst (hx : IsNilpotent x) : HasSubst (C x) := by
  change IsNilpotent (constantCoeff (C x))
  simpa using hx

/-- Evaluate by substituting the constant series and taking its constant coefficient. -/
def nilpotentSeriesEval (hx : IsNilpotent x) : PowerSeries R →+* R :=
  constantCoeff.comp (substAlgHom (nilpotentConstant_hasSubst hx)).toRingHom

/-- Evaluation is the constant coefficient after formal substitution. -/
theorem nilpotentSeriesEval_apply (hx : IsNilpotent x) (f : PowerSeries R) :
    nilpotentSeriesEval hx f = constantCoeff (f.subst (C x)) := by
  change constantCoeff ((substAlgHom (nilpotentConstant_hasSubst hx)) f) = _
  rw [coe_substAlgHom]

/-- Constants are fixed by nilpotent evaluation. -/
@[simp] theorem nilpotentSeriesEval_C (hx : IsNilpotent x) (a : R) :
    nilpotentSeriesEval hx (C a) = a := by
  simp [nilpotentSeriesEval, coe_substAlgHom, subst_C, constantCoeff_eq]

/-- The formal variable evaluates to the specified nilpotent. -/
@[simp] theorem nilpotentSeriesEval_X (hx : IsNilpotent x) :
    nilpotentSeriesEval hx X = x := by
  simp [nilpotentSeriesEval, substAlgHom_X]

/-- Polynomial evaluation agrees with the algebraic series evaluation. -/
theorem nilpotentSeriesEval_polynomial (hx : IsNilpotent x) (f : Polynomial R) :
    nilpotentSeriesEval hx f = f.eval x := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa using congrArg₂ (· + ·) hf hg
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp

/-- Any truncation beyond a nilpotence bound evaluates to exactly the full series. -/
theorem nilpotentSeriesEval_trunc (hx : IsNilpotent x) (r : ℕ) (hr : x ^ r = 0)
    (f : PowerSeries R) : nilpotentSeriesEval hx f = (trunc r f).eval x := by
  have hd : X ^ r ∣ f - (trunc r f : PowerSeries R) := by
    apply X_pow_dvd_iff.mpr
    intro n hn
    simp [coeff_trunc, hn]
  obtain ⟨g, hg⟩ := hd
  have he := congrArg (nilpotentSeriesEval hx) hg
  rw [map_sub, map_mul, map_pow, nilpotentSeriesEval_X, hr, zero_mul,
    nilpotentSeriesEval_polynomial, sub_eq_zero] at he
  exact he

/-- The nilpotent evaluation is an actual finite sum with no convergence assumptions. -/
theorem nilpotentSeriesEval_eq_sum (hx : IsNilpotent x) (r : ℕ) (hr : x ^ r = 0)
    (f : PowerSeries R) :
    nilpotentSeriesEval hx f = ∑ i ∈ Finset.range r, coeff i f * x ^ i := by
  rw [nilpotentSeriesEval_trunc hx r hr]
  exact eval₂_trunc_eq_sum_range x (RingHom.id R) r f

end PadicHodgeTheory
