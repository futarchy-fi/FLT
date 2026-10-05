/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalAddition

/-!
# Congruence of formal operations under arbitrary evaluation

Equal evaluated parameters give equal coordinates and equal formal sums.
The proof uses the integral divided difference and uniqueness of unit inverses;
no injectivity, completeness, or continuity of the ring map is required.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}
variable (W : WeierstrassCurve R) (f : MvPowerSeries σ R →+* S)

/-- The integral divided difference makes coordinates depend only on parameter values. -/
theorem evaluation_coordinate_congr {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) (h : f t = f v) :
    f (coordinate W t) = f (coordinate W v) := by
  have he := congrArg f (slope_mul_sub W ht hv)
  apply sub_eq_zero.mp
  simpa only [map_mul, map_sub, h, sub_self, mul_zero] using he.symm

/-- Evaluated normalized unit inverses depend only on their denominator value. -/
theorem evaluation_inverse_congr {g h : MvPowerSeries σ R}
    (hg : g.constantCoeff = 1) (hh : h.constantCoeff = 1) (he : f g = f h) :
    f (MvPowerSeries.invOfUnit g 1) = f (MvPowerSeries.invOfUnit h 1) := by
  have hu := ((MvPowerSeries.isUnit_iff_constantCoeff.mpr (hg ▸ isUnit_one)).map f)
  apply hu.mul_left_cancel
  have h₁ := congrArg f (MvPowerSeries.mul_invOfUnit g 1 hg)
  have h₂ := congrArg f (MvPowerSeries.mul_invOfUnit h 1 hh)
  simpa only [map_mul, map_one, he] using h₁.trans h₂.symm

/-- Evaluated secant slopes respect equal parameter values. -/
theorem evaluation_slope_congr {t v t' v' : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0)
    (ht' : t'.constantCoeff = 0) (hv' : v'.constantCoeff = 0)
    (he : f t = f t') (he' : f v = f v') : f (slope W t v) = f (slope W t' v') := by
  have hs := evaluation_coordinate_congr W f ht ht' he
  have hs' := evaluation_coordinate_congr W f hv hv' he'
  have hd : f (secantDenominator W t v) = f (secantDenominator W t' v') := by
    simp only [secantDenominator, differenceUnit, map_sub, map_one, map_mul, map_add,
      map_pow, he, hs, hs']
  have hi := evaluation_inverse_congr f (constantCoeff_secantDenominator W ht hv)
    (constantCoeff_secantDenominator W ht' hv') hd
  simp only [slope, map_mul, hi, secantNumerator, map_add, map_pow, he, he', hs']

/-- Evaluated third-intersection parameters respect equal input values. -/
theorem evaluation_thirdParameter_congr {t v t' v' : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0)
    (ht' : t'.constantCoeff = 0) (hv' : v'.constantCoeff = 0)
    (he : f t = f t') (he' : f v = f v') :
    f (thirdParameter W t v) = f (thirdParameter W t' v') := by
  have hs := evaluation_slope_congr W f ht hv ht' hv' he he'
  have hc := evaluation_coordinate_congr W f ht ht' he
  have hn : f (intercept W t v) = f (intercept W t' v') := by
    simp only [intercept, map_sub, map_mul, hc, hs, he]
  have hl : f (cubicLeading (curve W) (slope W t v)) =
      f (cubicLeading (curve W) (slope W t' v')) := by
    simp only [cubicLeading, map_add, map_mul, map_pow, map_one, hs]
  have hi := evaluation_inverse_congr f (constantCoeff_cubicLeading W ht hv)
    (constantCoeff_cubicLeading W ht' hv') hl
  simp only [thirdParameter, map_sub, map_mul, map_neg, hi, he, he', cubicQuadratic,
    map_add, map_ofNat, map_pow, hs, hn]

/-- Evaluated formal inverses respect equal parameter values. -/
theorem evaluation_negate_congr {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) (he : f t = f v) :
    f (negate W t) = f (negate W v) := by
  have hc := evaluation_coordinate_congr W f ht hv he
  have hd : f (negationDenominator (curve W) t (coordinate W t)) =
      f (negationDenominator (curve W) v (coordinate W v)) := by
    simp only [negationDenominator, map_sub, map_one, map_mul, he, hc]
  have hi := evaluation_inverse_congr f (constantCoeff_negationDenominator W ht)
    (constantCoeff_negationDenominator W hv) hd
  simp only [negate, negationUnitInv, map_mul, map_neg, he, hi]

/-- Arbitrary ring maps evaluate formal sums compatibly with equal input values. -/
theorem evaluation_add_congr {t v t' v' : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0)
    (ht' : t'.constantCoeff = 0) (hv' : v'.constantCoeff = 0)
    (he : f t = f t') (he' : f v = f v') : f (add W t v) = f (add W t' v') :=
  evaluation_negate_congr W f (constantCoeff_thirdParameter W ht hv)
    (constantCoeff_thirdParameter W ht' hv')
    (evaluation_thirdParameter_congr W f ht hv ht' hv' he he')

end FLT.Mazur.FormalInfinity
