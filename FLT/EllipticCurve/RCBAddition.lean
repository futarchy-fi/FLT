/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Polynomial certificates for the Renes–Costello–Batina addition law

These are the short Weierstrass formulas in equation (1) of Renes, Costello
and Batina, *Complete addition formulas for prime order elliptic curves*,
https://eprint.iacr.org/2015/1060. The identities are valid over arbitrary
commutative rings. Using them as a projective addition law also requires
nonvanishing of the output coordinates.
-/

@[expose] public section

namespace WeierstrassCurve.RCB
variable {R : Type*} [CommRing R]

/-- The X-coordinate of the RCB projective addition formula. -/
def addX (a b x1 y1 z1 x2 y2 z2 : R) : R :=
  (x1 * y2 + x2 * y1) * (y1 * y2 - a * (x1 * z2 + x2 * z1) - 3 * b * z1 * z2) -
    (y1 * z2 + y2 * z1) *
      (a * x1 * x2 + 3 * b * (x1 * z2 + x2 * z1) - a ^ 2 * z1 * z2)

/-- The Y-coordinate of the RCB projective addition formula. -/
def addY (a b x1 y1 z1 x2 y2 z2 : R) : R :=
  (3 * x1 * x2 + a * z1 * z2) *
      (a * x1 * x2 + 3 * b * (x1 * z2 + x2 * z1) - a ^ 2 * z1 * z2) +
    (y1 * y2 + a * (x1 * z2 + x2 * z1) + 3 * b * z1 * z2) *
      (y1 * y2 - a * (x1 * z2 + x2 * z1) - 3 * b * z1 * z2)

/-- The Z-coordinate of the RCB projective addition formula. -/
def addZ (a b x1 y1 z1 x2 y2 z2 : R) : R :=
  (y1 * z2 + y2 * z1) *
      (y1 * y2 + a * (x1 * z2 + x2 * z1) + 3 * b * z1 * z2) +
    (x1 * y2 + x2 * y1) * (3 * x1 * x2 + a * z1 * z2)

/-- On affine inputs, the RCB denominator is the numerator of the y-coordinate
of their difference. This identifies its exceptional locus away from equal x-coordinates. -/
theorem addZ_eq_difference_numerator (a b x1 y1 x2 y2 : R)
    (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) :
    addZ a b x1 y1 1 x2 y2 1 =
      -(y1 + y2) * (x1 * (x2 - x1) ^ 2 -
        ((y1 + y2) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) - y1 * (x2 - x1) ^ 3 := by
  unfold addZ
  linear_combination (-y1 - 2 * y2) * h1 + (-2 * y1 - y2) * h2

/-- The denominator on the diagonal is the usual doubled-point denominator. -/
theorem addZ_self (a b x y : R) (h : y ^ 2 = x ^ 3 + a * x + b) :
    addZ a b x y 1 x y 1 = (2 * y) ^ 3 := by
  unfold addZ
  linear_combination -6 * y * h

/-- Changing the sign of the second y-coordinate leaves the diagonal
Y-coordinate unchanged. This also covers pairs whose sum is infinity. -/
theorem addY_neg_self (a b x y : R) :
    addY a b x y 1 x (-y) 1 = addY a b x y 1 x y 1 := by
  unfold addY
  ring

/-- The x-coordinate agrees with the secant formula after clearing its denominator. -/
theorem addX_secant_identity (a b x1 y1 x2 y2 : R)
    (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) :
    addX a b x1 y1 1 x2 y2 1 * (x2 - x1) ^ 2 =
      addZ a b x1 y1 1 x2 y2 1 *
        ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2) := by
  unfold addX addZ
  linear_combination
    (-a * x1 * y1 - a * x1 * y2 - 2 * a * x2 * y1 + 3 * a * x2 * y2 - 3 * b * y1 + 2 * b * y2 -
      3 * x1 ^ 2 * x2 * y2 - 3 * x1 * x2 ^ 2 * y1 + 3 * x1 * x2 ^ 2 * y2 + 2 * x2 ^ 3 * y2 - y1
      ^ 2 * y2 + y1 * y2 ^ 2 + y2 ^ 3) * h1
    + (4 * a * x1 * y1 - a * x1 * y2 - a * x2 * y1 - a * x2 * y2 + 3 * b * y1 - 2 * b * y2 + 3 *
      x1 ^ 3 * y1 + x1 ^ 3 * y2 + 3 * x1 ^ 2 * x2 * y1 - 3 * x1 ^ 2 * x2 * y2 - 3 * x1 * x2 ^ 2
      * y1 - y1 * y2 ^ 2) * h2

/-- The y-coordinate agrees with the secant formula after clearing its denominator. -/
theorem addY_secant_identity (a b x1 y1 x2 y2 : R)
    (h1 : y1 ^ 2 = x1 ^ 3 + a * x1 + b)
    (h2 : y2 ^ 2 = x2 ^ 3 + a * x2 + b) :
    addY a b x1 y1 1 x2 y2 1 * (x2 - x1) ^ 3 =
      addZ a b x1 y1 1 x2 y2 1 *
        ((y2 - y1) * (x1 * (x2 - x1) ^ 2 -
          ((y2 - y1) ^ 2 - (x1 + x2) * (x2 - x1) ^ 2)) - y1 * (x2 - x1) ^ 3) := by
  unfold addY addZ
  linear_combination
    (-a ^ 2 * x1 ^ 2 - 2 * a ^ 2 * x1 * x2 - 4 * a * b * x1 - 2 * a * b * x2 - 6 * a * x1 ^ 2 *
      x2 ^ 2 - 4 * a * x1 * x2 ^ 3 - a * x1 * y1 ^ 2 + 5 * a * x1 * y2 ^ 2 + 4 * a * x2 ^ 4 - 2
      * a * x2 * y1 ^ 2 + 5 * a * x2 * y1 * y2 - 3 * a * x2 * y2 ^ 2 - 3 * b ^ 2 - 12 * b * x1 *
      x2 ^ 2 + 6 * b * x2 ^ 3 - 3 * b * y1 ^ 2 + 5 * b * y1 * y2 + 2 * b * y2 ^ 2 - 9 * x1 ^ 2 *
      x2 ^ 4 - 3 * x1 ^ 2 * x2 * y1 * y2 + 15 * x1 ^ 2 * x2 * y2 ^ 2 + 6 * x1 * x2 ^ 5 - 3 * x1
      * x2 ^ 2 * y1 ^ 2 + 6 * x1 * x2 ^ 2 * y1 * y2 - 15 * x1 * x2 ^ 2 * y2 ^ 2 + 2 * x2 ^ 3 *
      y1 * y2 + 2 * x2 ^ 3 * y2 ^ 2 - y1 ^ 3 * y2 + 2 * y1 ^ 2 * y2 ^ 2 - 2 * y2 ^ 4) * h1
    + (5 * a ^ 2 * x1 ^ 2 - 3 * a ^ 2 * x1 * x2 + a ^ 2 * x2 ^ 2 + 7 * a * b * x1 - a * b * x2 +
      a * x1 ^ 4 + 14 * a * x1 ^ 3 * x2 - 9 * a * x1 ^ 2 * x2 ^ 2 - 5 * a * x1 * y1 * y2 + a *
      x2 * y2 ^ 2 + 3 * b ^ 2 - 6 * b * x1 ^ 3 + 27 * b * x1 ^ 2 * x2 - 15 * b * x1 * x2 ^ 2 - 5
      * b * y1 * y2 + b * y2 ^ 2 + 9 * x1 ^ 5 * x2 - 6 * x1 ^ 4 * x2 ^ 2 - 2 * x1 ^ 3 * y1 * y2
      - 2 * x1 ^ 3 * y2 ^ 2 - 6 * x1 ^ 2 * x2 * y1 * y2 + 3 * x1 ^ 2 * x2 * y2 ^ 2 + 3 * x1 * x2
      ^ 2 * y1 * y2 + y1 * y2 ^ 3) * h2

/-- The diagonal x-coordinate agrees with the usual tangent formula. -/
theorem addX_self (a b x y : R) (h : y ^ 2 = x ^ 3 + a * x + b) :
    addX a b x y 1 x y 1 =
      2 * y * ((3 * x ^ 2 + a) ^ 2 - 8 * x * y ^ 2) := by
  unfold addX
  linear_combination 18 * x * y * h

/-- The diagonal y-coordinate agrees with the usual tangent formula. -/
theorem addY_self (a b x y : R) (h : y ^ 2 = x ^ 3 + a * x + b) :
    addY a b x y 1 x y 1 =
      (3 * x ^ 2 + a) * (4 * x * y ^ 2 - ((3 * x ^ 2 + a) ^ 2 - 8 * x * y ^ 2)) -
        8 * y ^ 4 := by
  unfold addY
  linear_combination (-3 * a * x + 9 * b - 27 * x ^ 3 + 9 * y ^ 2) * h

end WeierstrassCurve.RCB
