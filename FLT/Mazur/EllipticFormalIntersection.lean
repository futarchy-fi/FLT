/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalCubic

/-!
# The integral third intersection of the formal secant

The leading cubic coefficient is a unit at the origin. Vieta's formula therefore
constructs the third point over the coefficient ring, without inverting either
input parameter or their difference.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*} (W : WeierstrassCurve R)

/-- The third intersection parameter given by Vieta's formula. -/
noncomputable def thirdParameter (t v : MvPowerSeries σ R) : MvPowerSeries σ R :=
  -cubicQuadratic (curve W) (slope W t v) (intercept W t v) *
    MvPowerSeries.invOfUnit (cubicLeading (curve W) (slope W t v)) 1 - t - v

/-- The third intersection's s-coordinate, on the secant line. -/
noncomputable def thirdCoordinate (t v : MvPowerSeries σ R) : MvPowerSeries σ R :=
  slope W t v * thirdParameter W t v + intercept W t v

/-- The cubic leading coefficient is one at the origin. -/
@[simp] theorem constantCoeff_cubicLeading {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (cubicLeading (curve W) (slope W t v)).constantCoeff = 1 := by
  simp [cubicLeading, curve, constantCoeff_slope W ht hv]

/-- The quadratic coefficient vanishes at the origin. -/
@[simp] theorem constantCoeff_cubicQuadratic {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (cubicQuadratic (curve W) (slope W t v) (intercept W t v)).constantCoeff = 0 := by
  simp [cubicQuadratic, curve, constantCoeff_slope W ht hv, constantCoeff_intercept W ht]

/-- The third intersection stays in the formal neighborhood of infinity. -/
@[simp] theorem constantCoeff_thirdParameter {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (thirdParameter W t v).constantCoeff = 0 := by
  simp [thirdParameter, constantCoeff_cubicQuadratic W ht hv, ht, hv]

/-- The third s-coordinate also vanishes at the origin. -/
@[simp] theorem constantCoeff_thirdCoordinate {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (thirdCoordinate W t v).constantCoeff = 0 := by
  simp [thirdCoordinate, constantCoeff_thirdParameter W ht hv, constantCoeff_intercept W ht]

/-- The three intersection parameters satisfy Vieta's sum formula. -/
theorem thirdParameter_sum {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    cubicLeading (curve W) (slope W t v) * (thirdParameter W t v + t + v) +
      cubicQuadratic (curve W) (slope W t v) (intercept W t v) = 0 := by
  have h := MvPowerSeries.mul_invOfUnit (cubicLeading (curve W) (slope W t v)) 1
    (constantCoeff_cubicLeading W ht hv)
  unfold thirdParameter
  linear_combination
    -cubicQuadratic (curve W) (slope W t v) (intercept W t v) * h

/-- The constructed third intersection satisfies the Weierstrass chart equation. -/
theorem equation_third {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    Equation (curve W) (thirdParameter W t v) (thirdCoordinate W t v) := by
  have hq := slope_mul_denominator W ht hv
  unfold secantDenominator at hq
  rw [← line_left W t v, ← line_right W ht hv] at hq
  have hd := cubic_divided_relation (curve W) _ _ _ _ hq
  have he := equation_coordinate W ht
  rw [← line_left W t v, equation_line_iff] at he
  exact (equation_line_iff (curve W) _ _ _).mpr
    (cubic_third_root _ _ _ _ _ _ _ he hd (thirdParameter_sum W ht hv))

/-- The third s-coordinate is the same integral coordinate series at its parameter. -/
theorem thirdCoordinate_eq_coordinate {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    thirdCoordinate W t v = coordinate W (thirdParameter W t v) :=
  eq_coordinate W (constantCoeff_thirdParameter W ht hv)
    (constantCoeff_thirdCoordinate W ht hv) (equation_third W ht hv)

end FLT.Mazur.FormalInfinity
