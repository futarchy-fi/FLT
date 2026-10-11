/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Ordered monomials of weights two and three

The list starts with 1,x,y,x²,xy,x³,x²y and has one monomial in each
order 0,2,3,4,5,6,7,... . The exponent of y is at most one throughout.
-/

@[expose] public section
namespace FLT.Mazur.WeightedPoleMonomials

/-- The pole orders, with the missing order one omitted. -/
def order (i : ℕ) : ℕ := if i = 0 then 0 else i + 1

/-- The x exponent of the monomial at the specified position. -/
def xExponent (i : ℕ) : ℕ := if i % 2 = 1 then (i + 1) / 2 else (i - 2) / 2

/-- The y exponent is one precisely at positive even positions. -/
def yExponent (i : ℕ) : ℕ := if i = 0 ∨ i % 2 = 1 then 0 else 1

/-- The actual ordered monomials in the two given functions. -/
def monomial {R : Type*} [CommRing R] (x y : R) (i : ℕ) : R :=
  x ^ xExponent i * y ^ yExponent i

/-- The first monomial is the original constant one. -/
theorem monomial_zero {R : Type*} [CommRing R] (x y : R) : monomial x y 0 = 1 := by
  simp [monomial, xExponent, yExponent]

/-- These explicit exponents have exactly the listed weighted order. -/
theorem weightedOrder (i : ℕ) : 2 * xExponent i + 3 * yExponent i = order i := by
  unfold xExponent yExponent order
  split_ifs <;> omega

/-- Later positions have strictly larger pole orders. -/
theorem order_strictMono : StrictMono order := by
  intro i j hij
  unfold order
  split_ifs <;> omega

/-- Every positive position represents a nonconstant monomial. -/
theorem exponents_pos (i : ℕ) (hi : 0 < i) : 0 < xExponent i + yExponent i := by
  have hw := weightedOrder i
  have ho : order i = i + 1 := ite_eq_right (by omega)
  omega

/-- The first N listed orders have pole bound N. -/
theorem order_le (N : ℕ) (i : Fin N) : order i ≤ N := by
  unfold order
  split_ifs <;> omega

end FLT.Mazur.WeightedPoleMonomials
