/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Tactic.Ring

/-!
# Exact secant equation for the original pole-coordinate extraction

Subtract two cubic-denominator extraction identities. The coordinate error
has an explicit coefficient whose value at the coordinate node is the
original unit coefficient. No coordinate or smoothing parameter is cancelled.
-/

public section
namespace FLT.Mazur.NodePoleSecant
variable {R : Type*} [CommRing R]

/-- The divided difference of the original cubic marking denominator. -/
def cubic (x y : R) : R := x ^ 2 + x * y + y ^ 2 - 3 * (x + y) + 3

/-- The exact coordinate-error equation before any quotient or cancellation. -/
theorem equation (x y a u v : R)
    (hx : (x - 1) ^ 3 * u = a * x) (hy : (y - 1) ^ 3 * v = a * y) :
    (a - cubic x y * v) * (x - y) = (x - 1) ^ 3 * (u - v) := by
  calc
    _ = a * x - a * y - ((x - 1) ^ 3 - (y - 1) ^ 3) * v := by
      unfold cubic
      ring
    _ = _ := by rw [← hx, ← hy]; ring

/-- Equal pole combinations force equal coordinates where this explicit coefficient is a unit. -/
theorem eq_of_isUnit (x y a u v : R)
    (hx : (x - 1) ^ 3 * u = a * x) (hy : (y - 1) ^ 3 * v = a * y)
    (ha : IsUnit (a - cubic x y * v)) (huv : u = v) : x = y := by
  have he := equation x y a u v hx hy
  rw [huv, sub_self, mul_zero] at he
  exact sub_eq_zero.mp ((ha.mul_right_eq_zero).mp he)

/-- At the original coordinate node, the pole combination has zero image. -/
theorem combination_node {S : Type*} [CommRing S] (f : R →+* S)
    (x a u : R) (hx : (x - 1) ^ 3 * u = a * x) (hfx : f x = 0) : f u = 0 := by
  have he := congrArg f hx
  simpa only [map_mul, map_pow, map_sub, map_one, hfx, zero_sub,
    show (-1 : S) ^ 3 = -1 by ring, neg_mul, one_mul, mul_zero, neg_eq_zero] using he

/-- The secant coefficient retains the original unit value at the same node. -/
theorem coefficient_node {S : Type*} [CommRing S] (f : R →+* S)
    (x y a v : R) (hy : (y - 1) ^ 3 * v = a * y) (hfy : f y = 0) :
    f (a - cubic x y * v) = f a := by
  rw [map_sub, map_mul, combination_node f y a v hy hfy, mul_zero, sub_zero]

end FLT.Mazur.NodePoleSecant
