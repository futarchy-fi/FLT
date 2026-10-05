/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalEvaluationAddition

/-!
# Integral formal multiplication by integers

Negative integers use the constructed formal inverse. Arbitrary field evaluation
intertwines this operation with actual integer scalar multiplication.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*} (W : WeierstrassCurve R)

/-- Formal multiplication by an integer, using normalized negation for negative scalars. -/
noncomputable def integerMultiply : ℤ → MvPowerSeries σ R → MvPowerSeries σ R
  | .ofNat n, t => multiply W n t
  | .negSucc n, t => negate W (multiply W (n + 1) t)

/-- The integral multiplication-by-an-integer series. -/
noncomputable def integerMultiplicationSeries (n : ℤ) : PowerSeries R :=
  integerMultiply W n PowerSeries.X

/-- Integer multiplication preserves zero constant coefficients. -/
@[simp] theorem constantCoeff_integerMultiply (n : ℤ) {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) : (integerMultiply W n t).constantCoeff = 0 := by
  cases n with
  | ofNat n => exact constantCoeff_multiply W n ht
  | negSucc n => exact constantCoeff_negate W (constantCoeff_multiply W (n + 1) ht)

/-- The linear coefficient of multiplication by an integer is that integer. -/
@[simp] theorem coeff_one_integerMultiplicationSeries (n : ℤ) :
    PowerSeries.coeff 1 (integerMultiplicationSeries W n) = n := by
  have hx : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by
    simp [PowerSeries.X]
  cases n with
  | ofNat n =>
    simpa only [integerMultiplicationSeries, integerMultiply, multiplicationSeries,
      Int.ofNat_eq_natCast, Int.cast_natCast] using coeff_one_multiplicationSeries W n
  | negSucc n =>
    simp only [integerMultiplicationSeries, integerMultiply,
      coeff_one_negate W (constantCoeff_multiply W (n + 1) hx),
      coeff_one_multiply W (n + 1) hx, PowerSeries.coeff_one_X, mul_one, Int.cast_negSucc]

/-- The quadratic remainder also holds for negative integer scalars. -/
theorem X_sq_dvd_integerMultiplicationSeries_sub_linear (n : ℤ) :
    PowerSeries.X ^ 2 ∣ integerMultiplicationSeries W n -
      PowerSeries.C (n : R) * PowerSeries.X := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro m hm
  interval_cases m
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff,
      integerMultiplicationSeries, PowerSeries.X]
  · simp

/-- Arbitrary field evaluation preserves the constructed formal inverse. -/
theorem evaluationPoint_negate {K : Type*} [Field K] (f : MvPowerSeries σ R →+* K)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    evaluationPoint W f (negate W t) (constantCoeff_negate W ht) =
      -evaluationPoint W f t ht := by
  have h := evaluationPoint_add W f ht (constantCoeff_negate W ht)
  have hz : evaluationPoint W f (add W t (negate W t))
      (constantCoeff_add W ht (constantCoeff_negate W ht)) = 0 := by
    simpa only [add_negate W ht] using (evaluationPoint_zero W f)
  rw [hz] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Arbitrary evaluation computes actual integer scalar multiplication. -/
theorem evaluationPoint_integerMultiply {K : Type*} [Field K]
    (f : MvPowerSeries σ R →+* K) (n : ℤ) {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) :
    evaluationPoint W f (integerMultiply W n t) (constantCoeff_integerMultiply W n ht) =
      n • evaluationPoint W f t ht := by
  cases n with
  | ofNat n =>
    simpa only [integerMultiply, Int.ofNat_eq_natCast, natCast_zsmul] using
      evaluationPoint_multiply W f n ht
  | negSucc n =>
    simp only [integerMultiply, evaluationPoint_negate W f (constantCoeff_multiply W (n + 1) ht),
      evaluationPoint_multiply W f (n + 1) ht, negSucc_zsmul]

end FLT.Mazur.FormalInfinity
