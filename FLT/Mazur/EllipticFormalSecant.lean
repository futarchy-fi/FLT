/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalCoordinates

/-!
# An integral secant in the formal infinity chart

Subtracting the two chart equations gives the divided difference without dividing
by the difference of parameters. The only denominator has constant coefficient
one, so this construction works over every commutative ring, including on the
diagonal. The line through the two formal points has integral slope and intercept.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The numerator in the implicit divided-difference formula. -/
def secantNumerator (W : WeierstrassCurve R) (t v u : R) : R :=
  t ^ 2 + t * v + v ^ 2 + W.a₁ * u + W.a₂ * (t + v) * u + W.a₄ * u ^ 2

/-- Subtracting the chart equations factors out the difference of parameters. -/
theorem secant_difference (W : WeierstrassCurve R) {t v s u : R}
    (hs : Equation W t s) (hu : Equation W v u) :
    differenceUnit W t s u * (s - u) = (t - v) * secantNumerator W t v u := by
  unfold Equation at hs hu
  unfold differenceUnit secantNumerator
  linear_combination hs - hu

/-- The unit denominator of the formal secant. -/
noncomputable def secantDenominator (W : WeierstrassCurve R) (t v : MvPowerSeries σ R) :
    MvPowerSeries σ R := differenceUnit (curve W) t (coordinate W t) (coordinate W v)

/-- The secant denominator is one at the origin. -/
@[simp] theorem constantCoeff_secantDenominator (W : WeierstrassCurve R)
    {t v : MvPowerSeries σ R} (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (secantDenominator W t v).constantCoeff = 1 := by
  simp [secantDenominator, differenceUnit, curve, ht, constantCoeff_coordinate W ht,
    constantCoeff_coordinate W hv]

/-- Integral slope of the secant, including coincident parameters. -/
noncomputable def slope (W : WeierstrassCurve R) (t v : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  secantNumerator (curve W) t v (coordinate W v) *
    MvPowerSeries.invOfUnit (secantDenominator W t v) 1

/-- Integral intercept of the secant. -/
noncomputable def intercept (W : WeierstrassCurve R) (t v : MvPowerSeries σ R) :
    MvPowerSeries σ R := coordinate W t - slope W t v * t

/-- Clearing the unit denominator recovers the defining slope equation. -/
theorem slope_mul_denominator (W : WeierstrassCurve R) {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    slope W t v * secantDenominator W t v =
      secantNumerator (curve W) t v (coordinate W v) := by
  unfold slope
  rw [mul_assoc, MvPowerSeries.invOfUnit_mul _ 1
    (constantCoeff_secantDenominator W ht hv), mul_one]

/-- The slope has zero constant coefficient. -/
@[simp] theorem constantCoeff_slope (W : WeierstrassCurve R)
    {t v : MvPowerSeries σ R} (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (slope W t v).constantCoeff = 0 := by
  simp [slope, secantNumerator, curve, ht, hv, constantCoeff_coordinate W hv]

/-- The intercept has zero constant coefficient. -/
@[simp] theorem constantCoeff_intercept (W : WeierstrassCurve R)
    {t v : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    (intercept W t v).constantCoeff = 0 := by
  simp [intercept, ht, constantCoeff_coordinate W ht]

/-- The slope is the divided difference of the actual coordinate series. -/
theorem slope_mul_sub (W : WeierstrassCurve R) {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    slope W t v * (t - v) = coordinate W t - coordinate W v := by
  have hd := MvPowerSeries.mul_invOfUnit (secantDenominator W t v) 1
    (constantCoeff_secantDenominator W ht hv)
  have he := secant_difference (curve W) (equation_coordinate W ht) (equation_coordinate W hv)
  change secantDenominator W t v * _ = _ at he
  calc
    _ = ((t - v) * secantNumerator (curve W) t v (coordinate W v)) *
        MvPowerSeries.invOfUnit (secantDenominator W t v) 1 := by unfold slope; ring
    _ = (coordinate W t - coordinate W v) *
        (secantDenominator W t v * MvPowerSeries.invOfUnit (secantDenominator W t v) 1) := by
      rw [← he]
      ring
    _ = _ := by rw [hd, mul_one]

/-- The first formal point lies on the integral secant line. -/
theorem line_left (W : WeierstrassCurve R) (t v : MvPowerSeries σ R) :
    slope W t v * t + intercept W t v = coordinate W t := by
  unfold intercept
  ring

/-- The second formal point lies on the same line. -/
theorem line_right (W : WeierstrassCurve R) {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    slope W t v * v + intercept W t v = coordinate W v := by
  have h := slope_mul_sub W ht hv
  unfold intercept
  linear_combination -h

end FLT.Mazur.FormalInfinity
