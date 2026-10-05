/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalAddition
public import FLT.Mazur.EllipticFormalProjective
public import FLT.Mazur.EllipticFormalSecantComparison

/-!
# Formal addition and the projective secant

An explicit scalar relates the polynomial projective secant output to the
normalized representative of formal addition. Its unit factors have constant
coefficient one; only the difference of the two parameters can vanish.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*} (W : WeierstrassCurve R)

/-- The unnormalized inverse representative differs by the negation unit. -/
theorem negation_representative {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    ![t, negationDenominator (curve W) t (coordinate W t), coordinate W t] =
      -negationDenominator (curve W) t (coordinate W t) • representative W (negate W t) := by
  have hu := negationDenominator_mul_inv W ht
  rw [WeierstrassCurve.Projective.smul_fin3]
  change ![t, _, coordinate W t] = ![_ * negate W t, _ * (-1), _ * coordinate W (negate W t)]
  rw [coordinate_negate W ht]
  have hx : negationDenominator (curve W) t (coordinate W t) * t *
      negationUnitInv W t = t := by linear_combination t * hu
  have hs : negationDenominator (curve W) t (coordinate W t) * coordinate W t *
      negationUnitInv W t = coordinate W t := by linear_combination (coordinate W t) * hu
  simp only [negate, neg_mul_neg, mul_one, ← mul_assoc, hx, hs]

/-- Scale relating the projective secant to normalized formal addition. -/
noncomputable def additionScale (t v : MvPowerSeries σ R) : MvPowerSeries σ R :=
  -((t - v) ^ 3 * cubicLeading (curve W) (slope W t v)) *
    negationDenominator (curve W) (thirdParameter W t v)
      (coordinate W (thirdParameter W t v))

/-- The projective secant formula represents the constructed formal sum. -/
theorem addXYZ_representative {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (curve W).toProjective.addXYZ (representative W t) (representative W v) =
      additionScale W t v • representative W (add W t v) := by
  have hq := slope_mul_denominator W ht hv
  unfold secantDenominator at hq
  rw [← line_left W t v, ← line_right W ht hv] at hq
  have hd := cubic_divided_relation (curve W) _ _ _ _ hq
  have he := equation_coordinate W ht
  rw [← line_left W t v, equation_line_iff] at he
  have hp := secant_projectiveXYZ (curve W) _ _ _ _ _ he hd (thirdParameter_sum W ht hv)
  rw [line_left W t v, line_right W ht hv] at hp
  change (curve W).toProjective.addXYZ (representative W t) (representative W v) = _ at hp
  change _ = _ • ![thirdParameter W t v,
    negationDenominator (curve W) (thirdParameter W t v) (thirdCoordinate W t v),
    thirdCoordinate W t v] at hp
  rw [thirdCoordinate_eq_coordinate W ht hv,
    negation_representative W (constantCoeff_thirdParameter W ht hv)] at hp
  simpa only [smul_smul, mul_neg, neg_mul, additionScale, add] using hp

/-- The scale cannot vanish at distinct parameters over a domain. -/
theorem additionScale_ne_zero [IsDomain R] {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) (htv : t ≠ v) :
    additionScale W t v ≠ 0 := by
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr htv))
      (MvPowerSeries.isUnit_iff_constantCoeff.mpr
        (constantCoeff_cubicLeading W ht hv ▸ isUnit_one)).ne_zero
  · exact (MvPowerSeries.isUnit_iff_constantCoeff.mpr
      (constantCoeff_negationDenominator W (constantCoeff_thirdParameter W ht hv) ▸
        isUnit_one)).ne_zero

end FLT.Mazur.FormalInfinity
