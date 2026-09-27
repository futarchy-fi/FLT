/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.RCBAddition
public import FLT.EllipticCurve.OddTorsionChart
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
/-!
# Nonvanishing of RCB addition on odd torsion

On a short Weierstrass curve in characteristic different from two, the RCB
Y-coordinate is nonzero when both the sum and difference are odd torsion.
This includes the diagonal and inverse pairs, whose sums can be infinity.
-/

@[expose] public section

namespace WeierstrassCurve.RCB
variable {k : Type*} [Field k] [DecidableEq k]
    (E : WeierstrassCurve k) [E.IsShortNF]
omit [DecidableEq k] in
/-- The equation of a short Weierstrass model in affine coordinates. -/
theorem short_equation {x y : k} (h : E.toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + E.a₄ * x + E.a₆ := by
  simpa [a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF] using
    (E.toAffine.equation_iff x y).mp h
/-- The y-coordinate of a nonzero odd-torsion point on a short model is nonzero. -/
theorem y_ne_zero_of_odd_torsion {x y : k} (h : E.toAffine.Nonsingular x y) {n : ℕ} (hn : Odd n)
    (ht : n • Affine.Point.some x y h = 0) : y ≠ 0 := by
  have hy := E.two_mul_y_add_ne_zero_of_odd_torsion h hn ht
  simp only [a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, add_zero] at hy
  exact (mul_ne_zero_iff.mp hy).2
/-- Off the diagonal in x, the RCB denominator detects two-torsion in the difference. -/
theorem addZ_eq_mul_difference_y {x1 y1 x2 y2 : k}
    (h1 : y1 ^ 2 = x1 ^ 3 + E.a₄ * x1 + E.a₆)
    (h2 : y2 ^ 2 = x2 ^ 3 + E.a₄ * x2 + E.a₆) (hx : x1 ≠ x2) :
    addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1 = (x2 - x1) ^ 3 *
      E.toAffine.addY x1 x2 y1 (E.toAffine.slope x1 x2 y1 (-y2)) := by
  rw [addZ_eq_difference_numerator _ _ _ _ _ _ h1 h2, Affine.addY, Affine.negY,
    Affine.negAddY, Affine.addX, Affine.slope_of_X_ne hx]
  simp only [toAffine, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF]
  field_simp [sub_ne_zero.mpr hx]
  ring
/-- Off the diagonal in x, the RCB y-coordinate scales the affine sum coordinate. -/
theorem addY_eq_mul_sum_y {x1 y1 x2 y2 : k}
    (h1 : y1 ^ 2 = x1 ^ 3 + E.a₄ * x1 + E.a₆)
    (h2 : y2 ^ 2 = x2 ^ 3 + E.a₄ * x2 + E.a₆) (hx : x1 ≠ x2) :
    addY E.a₄ E.a₆ x1 y1 1 x2 y2 1 = addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1 *
      E.toAffine.addY x1 x2 y1 (E.toAffine.slope x1 x2 y1 y2) := by
  have hn : E.toAffine.addY x1 x2 y1 (E.toAffine.slope x1 x2 y1 y2) *
      (x2 - x1) ^ 3 =
        (y2 - y1) * (x1 * (x2 - x1) ^ 2 -
          ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) - y1 * (x2 - x1) ^ 3 := by
    rw [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, Affine.slope_of_X_ne hx]
    simp only [toAffine, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF]
    field_simp [sub_ne_zero.mpr hx]
    ring
  apply (mul_left_inj' (pow_ne_zero 3 (sub_ne_zero.mpr hx.symm))).mp
  rw [addY_secant_identity _ _ _ _ _ _ h1 h2, ← hn, mul_assoc]

/-- The RCB Y-coordinate is nonzero for distinct x-coordinates when sum and difference have odd order. -/
theorem addY_ne_zero_of_X_ne {x1 y1 x2 y2 : k}
    (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2)
    {n : ℕ} (hn : Odd n)
    (hs : n • (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) = 0)
    (hd : n • (Affine.Point.some x1 y1 h1 - Affine.Point.some x2 y2 h2) = 0)
    (hx : x1 ≠ x2) : addY E.a₄ E.a₆ x1 y1 1 x2 y2 1 ≠ 0 := by
  have hn2 : E.toAffine.Nonsingular x2 (-y2) := by
    simpa only [Affine.negY, toAffine, a₁_of_isShortNF, a₃_of_isShortNF,
      zero_mul, sub_zero] using (Affine.nonsingular_neg ..).mpr h2
  have hdiff : n • (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 (-y2) hn2) = 0 := by
    simpa only [sub_eq_add_neg, Affine.Point.neg_some, Affine.negY, toAffine,
      a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero, neg_zero, add_zero] using hd
  rw [Affine.Point.add_of_X_ne hx] at hdiff hs
  have hyd := y_ne_zero_of_odd_torsion E _ hn hdiff
  have hys := y_ne_zero_of_odd_torsion E _ hn hs
  have hz : addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1 ≠ 0 := by
    rw [addZ_eq_mul_difference_y E (short_equation E h1.1) (short_equation E h2.1) hx]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hx.symm)) hyd
  rw [addY_eq_mul_sum_y E (short_equation E h1.1) (short_equation E h2.1) hx]
  exact mul_ne_zero hz hys

/-- The RCB Y-coordinate on the diagonal is nonzero when twice the input has odd order. -/
theorem addY_self_ne_zero [NeZero (2 : k)] {x y : k}
    (h : E.toAffine.Nonsingular x y) {n : ℕ} (hn : Odd n)
    (ht : n • (Affine.Point.some x y h + Affine.Point.some x y h) = 0) :
    addY E.a₄ E.a₆ x y 1 x y 1 ≠ 0 := by
  by_cases hy : y = 0
  · subst y
    have hd : 3 * x ^ 2 + E.a₄ ≠ 0 := by
      have hd := (E.toAffine.nonsingular_iff' x 0).mp h |>.2
      simpa only [toAffine, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
        zero_mul, mul_zero, zero_add, add_zero, zero_sub, ne_eq, neg_eq_zero,
        not_true_eq_false, or_false] using hd
    rw [addY_self _ _ _ _ (short_equation E h.1)]
    simpa using mul_ne_zero hd (pow_ne_zero 2 hd)
  · have htwo : (2 : k) ≠ 0 := NeZero.ne _
    have hneg : y ≠ E.toAffine.negY x y := by
      simp only [Affine.negY, toAffine, a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero]
      intro he
      apply mul_ne_zero htwo hy
      linear_combination he
    rw [Affine.Point.add_self_of_Y_ne hneg] at ht
    have hys := y_ne_zero_of_odd_torsion E _ hn ht
    have he : addY E.a₄ E.a₆ x y 1 x y 1 = (2 * y) ^ 3 *
        E.toAffine.addY x x y (E.toAffine.slope x x y y) := by
      rw [addY_self _ _ _ _ (short_equation E h.1), Affine.addY, Affine.negY,
        Affine.negAddY, Affine.addX, Affine.slope_of_Y_ne rfl hneg]
      simp only [Affine.negY, toAffine, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
        zero_mul, add_zero, sub_zero, sub_neg_eq_add, ← two_mul]
      field_simp
      ring
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero htwo hy)) hys

/-- The RCB Y-coordinate is nonzero on every pair whose sum and difference are odd torsion. -/
theorem addY_ne_zero_of_odd_sum_diff [NeZero (2 : k)] {x1 y1 x2 y2 : k}
    (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2)
    {n : ℕ} (hn : Odd n)
    (hs : n • (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) = 0)
    (hd : n • (Affine.Point.some x1 y1 h1 - Affine.Point.some x2 y2 h2) = 0) :
    addY E.a₄ E.a₆ x1 y1 1 x2 y2 1 ≠ 0 := by
  by_cases hx : x1 = x2
  · subst x2
    have he : y1 ^ 2 = y2 ^ 2 := (short_equation E h1.1).trans (short_equation E h2.1).symm
    obtain he | he := sq_eq_sq_iff_eq_or_eq_neg.mp he
    · subst y2
      exact addY_self_ne_zero E h1 hn hs
    · have he' : y2 = -y1 := by rw [he, neg_neg]
      subst y2
      rw [addY_neg_self]
      apply addY_self_ne_zero E h1 hn
      simpa only [sub_eq_add_neg, Affine.Point.neg_some, Affine.negY, toAffine,
        a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero, neg_zero, add_zero,
        neg_neg] using hd
  · exact addY_ne_zero_of_X_ne E h1 h2 hn hs hd hx

end WeierstrassCurve.RCB
