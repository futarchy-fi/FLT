/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Translation by two-torsion on the Y chart

For a short Weierstrass equation, write `u = X/Y`, `v = Z/Y`.
Translation by `(ξ,0)` is polynomial in this chart, including at infinity.
The formulas below require no divisions over the coefficient ring.
-/

@[expose] public section

namespace WeierstrassCurve.TwoTorsionChart
variable {R : Type*} [CommRing R]

/-- The quadratic factor of the short Weierstrass cubic after removing `X - ξ Z`. -/
def factor (a ξ u v : R) : R := u ^ 2 + ξ * u * v + (a + ξ ^ 2) * v ^ 2

/-- The translated x-coordinate in the chart where Y is invertible. -/
def translateX (a ξ u v : R) : R := ξ + (3 * ξ ^ 2 + a) * factor a ξ u v

/-- The translated y-coordinate in the chart where Y is invertible. -/
def translateY (a ξ u v : R) : R :=
  -(3 * ξ ^ 2 + a) * (u - ξ * v) *
    (1 + 3 * ξ * factor a ξ u v + (3 * ξ ^ 2 + a) * factor a ξ u v ^ 2)

/-- The Y-chart equation factors through the chosen two-torsion root. -/
theorem equation_factor (a b ξ u v : R)
    (hT : ξ ^ 3 + a * ξ + b = 0)
    (h : v = u ^ 3 + a * u * v ^ 2 + b * v ^ 3) :
    v = (u - ξ * v) * factor a ξ u v := by
  unfold factor
  linear_combination h + v ^ 3 * hT

/-- A second factorization removes the apparent pole in the translated y-coordinate. -/
theorem factor_eq_square (a b ξ u v : R)
    (hT : ξ ^ 3 + a * ξ + b = 0)
    (h : v = u ^ 3 + a * u * v ^ 2 + b * v ^ 3) :
    factor a ξ u v = (u - ξ * v) ^ 2 *
      (1 + 3 * ξ * factor a ξ u v + (3 * ξ ^ 2 + a) * factor a ξ u v ^ 2) := by
  have hf := equation_factor a b ξ u v hT h
  linear_combination (norm := (unfold factor at *; ring_nf))
    (3 * ξ * (u - ξ * v) + (3 * ξ ^ 2 + a) *
      (v + (u - ξ * v) * factor a ξ u v)) * hf

/-- The polynomial translation formulas satisfy the original affine cubic. -/
theorem translate_equation (a b ξ u v : R)
    (hT : ξ ^ 3 + a * ξ + b = 0)
    (h : v = u ^ 3 + a * u * v ^ 2 + b * v ^ 3) :
    translateY a ξ u v ^ 2 =
      translateX a ξ u v ^ 3 + a * translateX a ξ u v + b := by
  have hf := factor_eq_square a b ξ u v hT h
  unfold translateX translateY
  linear_combination -(3 * ξ ^ 2 + a) ^ 2 *
    (1 + 3 * ξ * factor a ξ u v + (3 * ξ ^ 2 + a) * factor a ξ u v ^ 2) * hf - hT

/-- Infinity is translated to the specified affine two-torsion point. -/
@[simp] theorem translateX_infinity (a ξ : R) : translateX a ξ 0 0 = ξ := by
  simp [translateX, factor]

/-- The translated y-coordinate at infinity is zero. -/
@[simp] theorem translateY_infinity (a ξ : R) : translateY a ξ 0 0 = 0 := by
  simp [translateY]

end WeierstrassCurve.TwoTorsionChart
