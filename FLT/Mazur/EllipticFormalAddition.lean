/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalNegation
public import FLT.Mazur.EllipticFormalSymmetry

/-!
# The integral elliptic addition candidate

Negating the third secant intersection gives an integral operation on formal
parameters. It is symmetric and has zero as identity. Associativity and comparison
with actual point addition are separate obligations; this is not yet a FormalGroup.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*} (W : WeierstrassCurve R)

/-- Integral formal addition candidate from the secant construction. -/
noncomputable def add (t v : MvPowerSeries σ R) : MvPowerSeries σ R :=
  negate W (thirdParameter W t v)

/-- The two-variable integral addition series. -/
noncomputable def additionSeries : MvPowerSeries (Fin 2) R :=
  add W (MvPowerSeries.X 0) (MvPowerSeries.X 1)

/-- Addition preserves zero constant coefficients. -/
@[simp] theorem constantCoeff_add {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (add W t v).constantCoeff = 0 :=
  constantCoeff_negate W (constantCoeff_thirdParameter W ht hv)

/-- The constructed addition series has zero constant coefficient. -/
@[simp] theorem constantCoeff_additionSeries : (additionSeries W).constantCoeff = 0 :=
  constantCoeff_add W (by simp) (by simp)

/-- The integral addition candidate is symmetric. -/
theorem add_comm {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) : add W t v = add W v t := by
  unfold add
  rw [thirdParameter_symm W ht hv]

/-- The origin has s-coordinate zero. -/
@[simp] theorem coordinate_zero : coordinate W (0 : MvPowerSeries σ R) = 0 := by
  exact PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_infinitySeries W)

/-- The secant through the origin has intercept zero. -/
@[simp] theorem intercept_zero {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    intercept W t 0 = 0 := by
  simpa using line_right W ht (show MvPowerSeries.constantCoeff (0 : MvPowerSeries σ R) = 0 by simp)

/-- Algebraic identity for the third point on a line through the origin. -/
theorem third_through_origin {l t w u : R}
    (ha : IsUnit (cubicLeading W l))
    (hq : cubicLeading W l * t ^ 2 + cubicQuadratic W l 0 * t - l = 0)
    (hw : cubicLeading W l * (w + t) + cubicQuadratic W l 0 = 0)
    (hu : negationDenominator W t (l * t) * u = 1) : w = -t * u := by
  apply sub_eq_zero.mp
  apply ha.mul_right_eq_zero.mp
  simp only [cubicLeading, cubicQuadratic, negationDenominator] at hq hw hu ⊢
  linear_combination hw + (W.a₁ + W.a₃ * l) * u * hq +
    ((1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3) * t +
      (W.a₁ * l + W.a₃ * l ^ 2)) * hu

/-- The third intersection on the line through infinity is the negative point. -/
theorem thirdParameter_zero {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    thirdParameter W t 0 = negate W t := by
  have hz : (0 : MvPowerSeries σ R).constantCoeff = 0 := by simp
  have hq := slope_mul_denominator W ht hz
  unfold secantDenominator at hq
  rw [← line_left W t 0, ← line_right W ht hz] at hq
  have hd := cubic_divided_relation (curve W) _ _ _ _ hq
  have hw := thirdParameter_sum W ht hz
  have hu := negationDenominator_mul_inv W ht
  have hl : slope W t 0 * t = coordinate W t := by
    simpa only [intercept_zero W ht, add_zero] using line_left W t 0
  rw [← hl] at hu
  apply third_through_origin (curve W) _ _ _ hu
  · exact MvPowerSeries.isUnit_iff_constantCoeff.mpr
      (constantCoeff_cubicLeading W ht hz ▸ isUnit_one)
  · simpa [intercept_zero W ht, cubicLinear, sub_eq_add_neg] using hd
  · simpa only [intercept_zero W ht, add_zero] using hw

/-- Zero is a right identity for integral formal addition. -/
@[simp] theorem add_zero {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    add W t 0 = t := by
  rw [add, thirdParameter_zero W ht, negate_negate W ht]

/-- Zero is a left identity for integral formal addition. -/
@[simp] theorem zero_add {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    add W 0 t = t := by
  rw [add_comm W (by simp) ht, add_zero W ht]

end FLT.Mazur.FormalInfinity
