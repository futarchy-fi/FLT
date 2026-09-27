/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.TwoTorsionChart
public import FLT.EllipticCurve.RCBPoints
public import FLT.EllipticCurve.OddTorsionOrder
/-!
# Comparing RCB coordinates with addition of elliptic-curve points

The RCB formula normalized by its Y-coordinate agrees with the Y chart of
the group sum. Polynomial two-torsion translation then recovers affine
coordinates, including when the sum is infinity.
-/

@[expose] public section

namespace WeierstrassCurve.RCB
variable {k : Type*} [Field k] [DecidableEq k]
    (E : WeierstrassCurve k) [E.IsShortNF]
/-- The RCB x-coordinate scales the affine sum coordinate off the x-diagonal. -/
theorem addX_eq_mul_sum_x {x1 y1 x2 y2 : k}
    (h1 : y1 ^ 2 = x1 ^ 3 + E.a₄ * x1 + E.a₆)
    (h2 : y2 ^ 2 = x2 ^ 3 + E.a₄ * x2 + E.a₆) (hx : x1 ≠ x2) :
    addX E.a₄ E.a₆ x1 y1 1 x2 y2 1 = addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1 *
      E.toAffine.addX x1 x2 (E.toAffine.slope x1 x2 y1 y2) := by
  have hn : E.toAffine.addX x1 x2 (E.toAffine.slope x1 x2 y1 y2) *
      (x2 - x1) ^ 2 = (y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2 := by
    rw [Affine.addX, Affine.slope_of_X_ne hx]
    simp only [toAffine, a₁_of_isShortNF, a₂_of_isShortNF]
    field_simp [sub_ne_zero.mpr hx]
    ring
  apply (mul_left_inj' (pow_ne_zero 2 (sub_ne_zero.mpr hx.symm))).mp
  rw [addX_secant_identity _ _ _ _ _ _ h1 h2, ← hn, mul_assoc]

/-- The diagonal RCB x-coordinate scales the usual doubled-point coordinate. -/
theorem addX_self_eq_mul [NeZero (2 : k)] {x y : k}
    (h : E.toAffine.Nonsingular x y) (hy : y ≠ 0) :
    addX E.a₄ E.a₆ x y 1 x y 1 = (2 * y) ^ 3 *
      E.toAffine.addX x x (E.toAffine.slope x x y y) := by
  have hneg : y ≠ E.toAffine.negY x y := by
    simp only [Affine.negY, toAffine, a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero]
    intro he
    apply mul_ne_zero (NeZero.ne (2 : k)) hy
    linear_combination he
  rw [addX_self _ _ _ _ (short_equation E h.1), Affine.addX,
    Affine.slope_of_Y_ne rfl hneg]
  simp only [Affine.negY, toAffine, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
    zero_mul, add_zero, sub_zero, sub_neg_eq_add, ← two_mul]
  field_simp
  ring

/-- The diagonal RCB y-coordinate scales the usual doubled-point coordinate. -/
theorem addY_self_eq_mul [NeZero (2 : k)] {x y : k}
    (h : E.toAffine.Nonsingular x y) (hy : y ≠ 0) :
    addY E.a₄ E.a₆ x y 1 x y 1 = (2 * y) ^ 3 *
      E.toAffine.addY x x y (E.toAffine.slope x x y y) := by
  have hneg : y ≠ E.toAffine.negY x y := by
    simp only [Affine.negY, toAffine, a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero]
    intro he
    apply mul_ne_zero (NeZero.ne (2 : k)) hy
    linear_combination he
  rw [addY_self _ _ _ _ (short_equation E h.1), Affine.addY, Affine.negY,
    Affine.negAddY, Affine.addX, Affine.slope_of_Y_ne rfl hneg]
  simp only [Affine.negY, toAffine, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
    zero_mul, add_zero, sub_zero, sub_neg_eq_add, ← two_mul]
  field_simp
  ring

omit [DecidableEq k] [E.IsShortNF] in
/-- Coordinates in the Y chart, with infinity represented by `(0,0)`. -/
def yChartCoordinates : E.toAffine.Point → k × k
  | .zero => (0, 0)
  | .some x y _ => (x / y, 1 / y)

/-- Normalizing the RCB output by Y gives the Y-chart coordinates of the group sum. -/
theorem normalized_add [NeZero (2 : k)] {x1 y1 x2 y2 : k}
    (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2)
    {n : ℕ} (hn : Odd n)
    (hs : n • (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) = 0)
    (hd : n • (Affine.Point.some x1 y1 h1 - Affine.Point.some x2 y2 h2) = 0) :
    (addX E.a₄ E.a₆ x1 y1 1 x2 y2 1 / addY E.a₄ E.a₆ x1 y1 1 x2 y2 1,
      addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1 / addY E.a₄ E.a₆ x1 y1 1 x2 y2 1) =
        yChartCoordinates E (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) := by
  have hY := addY_ne_zero_of_odd_sum_diff E h1 h2 hn hs hd
  by_cases hx : x1 = x2
  · subst x2
    have he : y1 ^ 2 = y2 ^ 2 := (short_equation E h1.1).trans (short_equation E h2.1).symm
    obtain he | he := sq_eq_sq_iff_eq_or_eq_neg.mp he
    · subst y2
      by_cases hy : y1 = 0
      · subst y1
        have hz : (0 : k) = E.toAffine.negY x1 0 := by
          simp [Affine.negY, toAffine]
        rw [Affine.Point.add_self_of_Y_eq hz]
        simp [yChartCoordinates, addX, addZ]
      · have hneg : y1 ≠ E.toAffine.negY x1 y1 := by
          simp only [Affine.negY, toAffine, a₁_of_isShortNF, a₃_of_isShortNF, zero_mul, sub_zero]
          intro he
          apply mul_ne_zero (NeZero.ne (2 : k)) hy
          linear_combination he
        rw [Affine.Point.add_self_of_Y_ne hneg]
        rw [addX_self_eq_mul E h1 hy, addY_self_eq_mul E h1 hy,
          addZ_self _ _ _ _ (short_equation E h1.1)]
        dsimp only [yChartCoordinates]
        apply Prod.ext <;> field_simp
    · have he' : y2 = -y1 := by rw [he, neg_neg]
      subst y2
      have hz : y1 = E.toAffine.negY x1 (-y1) := by simp [Affine.negY, toAffine]
      rw [Affine.Point.add_of_Y_eq rfl hz]
      have hX : addX E.a₄ E.a₆ x1 y1 1 x1 (-y1) 1 = 0 := by unfold addX; ring
      have hZ : addZ E.a₄ E.a₆ x1 y1 1 x1 (-y1) 1 = 0 := by unfold addZ; ring
      simp [hX, hZ, yChartCoordinates]
  · rw [Affine.Point.add_of_X_ne hx]
    have hZ : addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1 ≠ 0 := by
      rw [addY_eq_mul_sum_y E (short_equation E h1.1) (short_equation E h2.1) hx] at hY
      exact (mul_ne_zero_iff.mp hY).1
    rw [addX_eq_mul_sum_x E (short_equation E h1.1) (short_equation E h2.1) hx,
      addY_eq_mul_sum_y E (short_equation E h1.1) (short_equation E h2.1) hx]
    dsimp only [yChartCoordinates]
    apply Prod.ext <;> field_simp
end WeierstrassCurve.RCB

namespace WeierstrassCurve.TwoTorsionChart
variable {k : Type*} [Field k]
/-- On an affine point with nonzero y, the chart factor is the inverse of x minus
the two-torsion root. -/
theorem factor_div (a b ξ x y : k) (hT : ξ ^ 3 + a * ξ + b = 0)
    (h : y ^ 2 = x ^ 3 + a * x + b) (hy : y ≠ 0) (hx : x ≠ ξ) :
    factor a ξ (x / y) (1 / y) = (x - ξ)⁻¹ := by
  rw [inv_eq_one_div]
  apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
  unfold factor
  field_simp
  linear_combination -h - hT
/-- The polynomial translated y-coordinate agrees with the usual rational translation formula. -/
theorem translateY_div (a b ξ x y : k) (hT : ξ ^ 3 + a * ξ + b = 0)
    (h : y ^ 2 = x ^ 3 + a * x + b) (hy : y ≠ 0) (hx : x ≠ ξ)
    (hf : factor a ξ (x / y) (1 / y) = (x - ξ)⁻¹) :
    translateY a ξ (x / y) (1 / y) = -(3 * ξ ^ 2 + a) * y / (x - ξ) ^ 2 := by
  rw [translateY, hf]
  field_simp [sub_ne_zero.mpr hx]
  linear_combination (3 * ξ ^ 2 + a) * (h + hT)
variable [DecidableEq k] (E : WeierstrassCurve k) [E.IsShortNF]
/-- The polynomial chart translation agrees with addition by the
two-torsion point on affine inputs. -/
theorem translate_affine {ξ x y : k}
    (hT : E.toAffine.Nonsingular ξ 0) (h : E.toAffine.Nonsingular x y) (hy : y ≠ 0) :
    (translateX E.a₄ ξ (x / y) (1 / y), translateY E.a₄ ξ (x / y) (1 / y)) =
      (Affine.Point.some x y h + Affine.Point.some ξ 0 hT).coordinates := by
  have he := RCB.short_equation E h.1
  have ht : ξ ^ 3 + E.a₄ * ξ + E.a₆ = 0 := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using (RCB.short_equation E hT.1).symm
  have hx : x ≠ ξ := by
    intro hxe
    rw [hxe, ht] at he
    exact pow_ne_zero 2 hy he
  have hf := factor_div E.a₄ E.a₆ ξ x y ht he hy hx
  have hax : E.toAffine.addX x ξ (E.toAffine.slope x ξ y 0) =
      ξ + (3 * ξ ^ 2 + E.a₄) / (x - ξ) := by
    rw [Affine.addX, Affine.slope_of_X_ne hx]
    simp only [toAffine, a₁_of_isShortNF, a₂_of_isShortNF]
    field_simp [sub_ne_zero.mpr hx]
    linear_combination he + ht
  have hay : E.toAffine.addY x ξ y (E.toAffine.slope x ξ y 0) =
      -(3 * ξ ^ 2 + E.a₄) * y / (x - ξ) ^ 2 := by
    rw [Affine.addY, Affine.negY, Affine.negAddY, hax, Affine.slope_of_X_ne hx]
    simp only [toAffine, a₁_of_isShortNF, a₃_of_isShortNF]
    field_simp [sub_ne_zero.mpr hx]
    ring
  rw [Affine.Point.add_of_X_ne hx]
  dsimp only [Affine.Point.coordinates]
  apply Prod.ext
  · dsimp only [Prod.fst]
    rw [translateX, hf, hax, div_eq_mul_inv]
  · dsimp only [Prod.snd]
    rw [hay]
    exact translateY_div E.a₄ E.a₆ ξ x y ht he hy hx hf

/-- Polynomial translation on the Y chart agrees with addition by two-torsion
for every odd-torsion point. -/
theorem translate_odd_point {ξ : k} (hT : E.toAffine.Nonsingular ξ 0)
    (P : E.toAffine.Point) {n : ℕ} (hn : Odd n) (hP : n • P = 0) :
    (translateX E.a₄ ξ (RCB.yChartCoordinates E P).1 (RCB.yChartCoordinates E P).2,
      translateY E.a₄ ξ (RCB.yChartCoordinates E P).1 (RCB.yChartCoordinates E P).2) =
        (P + Affine.Point.some ξ 0 hT).coordinates := by
  cases P with
  | zero =>
    change (translateX E.a₄ ξ 0 0, translateY E.a₄ ξ 0 0) = (ξ, 0)
    simp
  | some x y h =>
    exact translate_affine E hT h (RCB.y_ne_zero_of_odd_torsion E h hn hP)
end WeierstrassCurve.TwoTorsionChart

namespace WeierstrassCurve.RCB
variable {k : Type*} [Field k] [DecidableEq k]
    (E : WeierstrassCurve k) [E.IsShortNF] [NeZero (2 : k)]
/-- RCB addition followed by polynomial chart translation gives the translated group sum. -/
theorem translated_normalized_add {ξ x1 y1 x2 y2 : k}
    (hT : E.toAffine.Nonsingular ξ 0)
    (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2)
    {n : ℕ} (hn : Odd n)
    (hs : n • (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) = 0)
    (hd : n • (Affine.Point.some x1 y1 h1 - Affine.Point.some x2 y2 h2) = 0) :
    let u := addX E.a₄ E.a₆ x1 y1 1 x2 y2 1 / addY E.a₄ E.a₆ x1 y1 1 x2 y2 1
    let v := addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1 / addY E.a₄ E.a₆ x1 y1 1 x2 y2 1
    (TwoTorsionChart.translateX E.a₄ ξ u v, TwoTorsionChart.translateY E.a₄ ξ u v) =
      (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2 +
        Affine.Point.some ξ 0 hT).coordinates := by
  have hc := TwoTorsionChart.translate_odd_point E hT
    (Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2) hn hs
  rw [← normalized_add E h1 h2 hn hs hd] at hc
  exact hc
end WeierstrassCurve.RCB
