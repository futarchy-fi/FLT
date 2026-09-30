/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Elimination of one and two Raynaud coordinates

For a one- or two-coordinate Raynaud presentation, eliminating the other
coordinate gives the root equation used in §3.4(6) of Raynaud's
*Schémas en groupes de type (p,...,p)*. An automorphism fixing the parameters
therefore has a root-of-unity ratio on each nonzero coordinate. Construction
of the presentation and identification of the reduced ratio are separate.
-/

@[expose] public section

namespace RaynaudParameters

variable {K : Type*} [Field K] {p : ℕ} {a b x y : K}

/-- Eliminate the linear factor in a one-coordinate presentation. -/
theorem coordinate_one (hp : 1 ≤ p) (hx : x ≠ 0)
    (h : x ^ p = a * x) : x ^ (p - 1) = a := by
  apply mul_right_cancel₀ hx
  simpa only [← pow_succ, Nat.sub_add_cancel hp] using h

/-- Eliminate the second coordinate in a cyclic two-coordinate presentation. -/
theorem coordinate_two (hp : 1 ≤ p) (hx : x ≠ 0)
    (hxy : x ^ p = a * y) (hyx : y ^ p = b * x) :
    x ^ (p * p - 1) = a ^ p * b := by
  apply coordinate_one (by nlinarith : 1 ≤ p * p) hx
  rw [pow_mul, hxy, mul_pow, hyx, mul_assoc]

/-- The two cyclic coordinates give the two Frobenius-conjugate root equations. -/
theorem coordinate_pair (hp : 1 ≤ p) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ^ p = a * y) (hyx : y ^ p = b * x) :
    x ^ (p * p - 1) = a ^ p * b ∧ y ^ (p * p - 1) = b ^ p * a :=
  ⟨coordinate_two hp hx hxy hyx, coordinate_two hp hy hyx hxy⟩

/-- Fixing the parameters makes the coordinate ratio a (p²−1)st root of unity. -/
theorem coordinate_ratio_pow (hp : 1 ≤ p) (hx : x ≠ 0)
    (hxy : x ^ p = a * y) (hyx : y ^ p = b * x)
    (σ : K ≃+* K) (ha : σ a = a) (hb : σ b = b) :
    (σ x / x) ^ (p * p - 1) = 1 := by
  have he := coordinate_two hp hx hxy hyx
  have hs : (σ x) ^ (p * p - 1) = x ^ (p * p - 1) := by
    rw [← map_pow, he, map_mul, map_pow, ha, hb]
  rw [div_pow, hs, div_self (pow_ne_zero _ hx)]

end RaynaudParameters
