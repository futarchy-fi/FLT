/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Ring.Units

/-!
# A unit-separated frame detects triangular coordinate maps

Two different abscissas and two different ordinates above one abscissa
rigidify triangular coordinates over any commutative ring. No invertibility
of the triangular coefficients and no characteristic restriction is needed.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassTriangularFrame

variable {R : Type*} [CommRing R]

/-- The two unit differences force all five triangular coefficients to be those of identity. -/
theorem coefficients_eq (r s t v w x y y' z q : R)
    (hxz : IsUnit (x - z)) (hyy : IsUnit (y - y'))
    (hx : r + s * x = x) (hz : r + s * z = z)
    (hy : t + v * x + w * y = y) (hy' : t + v * x + w * y' = y')
    (hq : t + v * z + w * q = q) :
    r = 0 ∧ s = 1 ∧ t = 0 ∧ v = 0 ∧ w = 1 := by
  have hs : s = 1 := by
    apply sub_eq_zero.mp
    apply (hxz.mul_left_eq_zero).mp
    linear_combination hx - hz
  have hw : w = 1 := by
    apply sub_eq_zero.mp
    apply (hyy.mul_left_eq_zero).mp
    linear_combination hy - hy'
  have hv : v = 0 := by
    apply (hxz.mul_left_eq_zero).mp
    linear_combination hy - hq - (y - q) * hw
  have hr : r = 0 := by simpa only [hs, one_mul, add_eq_right] using hx
  have ht : t = 0 := by
    simpa only [hv, hw, zero_mul, add_zero, one_mul, add_eq_right] using hy
  exact ⟨hr, hs, ht, hv, hw⟩

end FLT.Mazur.WeierstrassTriangularFrame
