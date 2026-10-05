/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalIntersection

/-!
# Symmetry of the integral secant construction

Both orientations satisfy the same slope equation with a unit denominator.
This proves symmetry over arbitrary coefficient rings without cancelling a
parameter difference, including on the diagonal.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*} (W : WeierstrassCurve R)

/-- Reversing the endpoints does not change the formal slope. -/
theorem slope_symm {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) : slope W t v = slope W v t := by
  have ha := slope_mul_denominator W ht hv
  have hb := slope_mul_sub W ht hv
  have hc : slope W t v * secantDenominator W v t =
      secantNumerator (curve W) v t (coordinate W t) := by
    unfold secantDenominator differenceUnit secantNumerator at ha ⊢
    linear_combination ha + ((curve W).a₁ + (curve W).a₂ * (t + v) +
      (curve W).a₄ * (coordinate W t + coordinate W v)) * hb
  have hd := slope_mul_denominator W hv ht
  apply sub_eq_zero.mp
  apply (isUnit_differenceUnit W hv
    (constantCoeff_coordinate W hv) (constantCoeff_coordinate W ht)).mul_right_eq_zero.mp
  change secantDenominator W v t * _ = 0
  linear_combination hc - hd

/-- Reversing the endpoints does not change the intercept. -/
theorem intercept_symm {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    intercept W t v = intercept W v t := by
  have h := slope_mul_sub W ht hv
  unfold intercept
  rw [slope_symm W hv ht]
  linear_combination -h

/-- Vieta's third intersection is symmetric in the input parameters. -/
theorem thirdParameter_symm {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    thirdParameter W t v = thirdParameter W v t := by
  unfold thirdParameter
  rw [slope_symm W hv ht, intercept_symm W hv ht]
  ring

/-- The third s-coordinate is also independent of the orientation of the secant. -/
theorem thirdCoordinate_symm {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    thirdCoordinate W t v = thirdCoordinate W v t := by
  unfold thirdCoordinate
  rw [slope_symm W hv ht, thirdParameter_symm W hv ht, intercept_symm W hv ht]

end FLT.Mazur.FormalInfinity
