/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalAddition

/-!
# First-order coefficients of elliptic formal operations

For zero-constant univariate inputs, the coordinate has order at least three,
the secant slope and intercept have zero linear term, negation reverses the
linear coefficient, and formal addition adds linear coefficients.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The formal s-coordinate is divisible by the cube of the parameter. -/
theorem cube_dvd_coordinate {σ : Type*} {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) : t ^ 3 ∣ coordinate W t := by
  unfold coordinate infinitySeries
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero ht),
    PowerSeries.subst_pow (PowerSeries.HasSubst.of_constantCoeff_zero ht),
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ht)]
  exact dvd_mul_right _ _

/-- The s-coordinate has no linear coefficient. -/
theorem coeff_one_coordinate {t : PowerSeries R} (ht : MvPowerSeries.constantCoeff t = 0) :
    PowerSeries.coeff 1 (coordinate W t) = 0 := by
  obtain ⟨u, hu⟩ := cube_dvd_coordinate W ht
  rw [hu, PowerSeries.coeff_one_mul]
  simp [PowerSeries.coeff_one_pow, PowerSeries.constantCoeff, ht]

/-- The integral secant slope has no linear coefficient. -/
theorem coeff_one_slope {t v : PowerSeries R}
    (ht : MvPowerSeries.constantCoeff t = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.coeff 1 (slope W t v) = 0 := by
  simp [slope, secantNumerator, curve, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    PowerSeries.constantCoeff, ht, hv, constantCoeff_coordinate W hv, coeff_one_coordinate W hv]

/-- The integral secant intercept has no linear coefficient. -/
theorem coeff_one_intercept {t v : PowerSeries R}
    (ht : MvPowerSeries.constantCoeff t = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.coeff 1 (intercept W t v) = 0 := by
  simp [intercept, PowerSeries.coeff_one_mul, PowerSeries.constantCoeff, ht,
    constantCoeff_slope W ht hv, coeff_one_coordinate W ht]

/-- Vieta's third parameter has the negative sum of the input linear coefficients. -/
theorem coeff_one_thirdParameter {t v : PowerSeries R}
    (ht : MvPowerSeries.constantCoeff t = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.coeff 1 (thirdParameter W t v) =
      -PowerSeries.coeff 1 t - PowerSeries.coeff 1 v := by
  simp [thirdParameter, cubicQuadratic, curve, PowerSeries.coeff_one_mul,
    PowerSeries.coeff_one_pow, PowerSeries.constantCoeff, constantCoeff_slope W ht hv,
    constantCoeff_intercept W ht, coeff_one_slope W ht hv, coeff_one_intercept W ht hv]

/-- Normalized negation reverses the linear coefficient. -/
theorem coeff_one_negate {t : PowerSeries R} (ht : MvPowerSeries.constantCoeff t = 0) :
    PowerSeries.coeff 1 (negate W t) = -PowerSeries.coeff 1 t := by
  simp [negate, negationUnitInv, PowerSeries.coeff_one_mul, PowerSeries.constantCoeff,
    MvPowerSeries.constantCoeff_invOfUnit, ht]

/-- Formal addition adds the input linear coefficients. -/
theorem coeff_one_add {t v : PowerSeries R}
    (ht : MvPowerSeries.constantCoeff t = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.coeff 1 (add W t v) = PowerSeries.coeff 1 t + PowerSeries.coeff 1 v := by
  rw [add, coeff_one_negate W (constantCoeff_thirdParameter W ht hv),
    coeff_one_thirdParameter W ht hv]
  ring

end FLT.Mazur.FormalInfinity
