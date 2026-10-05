/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalSubstitution

/-!
# Coefficient changes for integral elliptic addition

The coordinate, secant, third intersection, negation, and addition constructions
commute with every homomorphism of coefficient rings. This permits specialization
from the universal Weierstrass curve without any flatness assumption.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open MvPowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}
variable (W : WeierstrassCurve R) (f : R →+* S)

/-- Coefficient changes preserve the integral coordinate. -/
theorem map_coordinate {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    map f (coordinate W t) = coordinate (W.map f) (map f t) := by
  rw [coordinate, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero ht),
    infinitySeries_map, coordinate]

/-- The normalized inverse of a series with constant coefficient one is natural. -/
theorem map_normalizedInverse {g : MvPowerSeries σ R} (hg : g.constantCoeff = 1) :
    map f (invOfUnit g 1) = invOfUnit (map f g) 1 := by
  have hg' : (map f g).constantCoeff = 1 := by simp [hg]
  have h₁ := congrArg (map f) (mul_invOfUnit g 1 hg)
  have h₂ := mul_invOfUnit (map f g) 1 hg'
  simp only [map_mul, map_one] at h₁
  apply sub_eq_zero.mp
  apply (isUnit_iff_constantCoeff.mpr (hg' ▸ isUnit_one)).mul_right_eq_zero.mp
  linear_combination h₁ - h₂

/-- Coefficient changes preserve the secant denominator. -/
theorem map_secantDenominator {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    map f (secantDenominator W t v) = secantDenominator (W.map f) (map f t) (map f v) := by
  simp only [secantDenominator, differenceUnit, curve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_sub, map_one, map_mul, map_add, map_pow, map_C,
    map_coordinate W f ht, map_coordinate W f hv]

/-- Coefficient changes preserve the integral secant slope. -/
theorem map_slope {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    map f (slope W t v) = slope (W.map f) (map f t) (map f v) := by
  simp only [slope, map_mul, map_normalizedInverse f (constantCoeff_secantDenominator W ht hv),
    map_secantDenominator W f ht hv, secantNumerator, curve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, map_add, map_pow, map_C,
    map_coordinate W f hv]

/-- Coefficient changes preserve the integral secant intercept. -/
theorem map_intercept {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    map f (intercept W t v) = intercept (W.map f) (map f t) (map f v) := by
  simp only [intercept, map_sub, map_mul, map_coordinate W f ht, map_slope W f ht hv]

/-- Coefficient changes preserve the third intersection parameter. -/
theorem map_thirdParameter {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    map f (thirdParameter W t v) = thirdParameter (W.map f) (map f t) (map f v) := by
  simp only [thirdParameter, map_sub, map_mul, map_neg]
  rw [map_normalizedInverse f (constantCoeff_cubicLeading W ht hv)]
  simp only [cubicLeading, cubicQuadratic, curve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_add, map_mul, map_pow, map_one, map_ofNat, map_C,
    map_slope W f ht hv, map_intercept W f ht hv]

/-- Coefficient changes preserve normalized negation. -/
theorem map_negate {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    map f (negate W t) = negate (W.map f) (map f t) := by
  simp only [negate, negationUnitInv, map_mul, map_neg]
  rw [map_normalizedInverse f (constantCoeff_negationDenominator W ht)]
  simp only [negationDenominator, curve, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    map_sub, map_mul, map_one, map_C, map_coordinate W f ht]

/-- Coefficient changes preserve formal addition. -/
theorem map_addition {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    map f (add W t v) = add (W.map f) (map f t) (map f v) := by
  rw [add, map_negate W f (constantCoeff_thirdParameter W ht hv),
    map_thirdParameter W f ht hv, add]

/-- The integral addition series is natural in the coefficient ring. -/
theorem map_additionSeries : map f (additionSeries W) = additionSeries (W.map f) := by
  unfold additionSeries
  rw [map_addition W f (by simp) (by simp), map_X, map_X]

end FLT.Mazur.FormalInfinity
