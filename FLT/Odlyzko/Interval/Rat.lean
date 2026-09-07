/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Basic

/-!
# Rational interval arithmetic

Closed real intervals with rational endpoints, together with deliberately conservative arithmetic
operations.  Every operation comes with a membership theorem; division and reciprocal require an
explicit certificate that the denominator interval does not contain zero.
-/

@[expose] public section

namespace Odlyzko.Interval

/-- A nonempty closed interval with rational endpoints. -/
structure RatIvl where
  /-- Rational lower endpoint. -/
  lo : ℚ
  /-- Rational upper endpoint. -/
  hi : ℚ
  lo_le_hi : lo ≤ hi

namespace RatIvl

/-- The closed real interval represented by rational endpoints. -/
def carrier (I : RatIvl) : Set ℝ := Set.Icc I.lo I.hi

instance : CoeTC RatIvl (Set ℝ) := ⟨carrier⟩

@[simp]
theorem mem_coe {I : RatIvl} {x : ℝ} :
    x ∈ (I : Set ℝ) ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) :=
  Iff.rfl

theorem left_mem (I : RatIvl) : (I.lo : ℝ) ∈ (I : Set ℝ) := by
  exact ⟨le_rfl, Rat.cast_le.mpr I.lo_le_hi⟩

theorem right_mem (I : RatIvl) : (I.hi : ℝ) ∈ (I : Set ℝ) := by
  exact ⟨Rat.cast_le.mpr I.lo_le_hi, le_rfl⟩

/-- The largest absolute value of an endpoint. -/
def radius (I : RatIvl) : ℚ := max |I.lo| |I.hi|

theorem radius_nonneg (I : RatIvl) : 0 ≤ I.radius :=
  le_trans (abs_nonneg I.lo) (le_max_left _ _)

theorem abs_le_radius {I : RatIvl} {x : ℝ} (hx : x ∈ (I : Set ℝ)) :
    |x| ≤ (I.radius : ℝ) := by
  have hlo : (I.lo : ℝ) ≤ x := hx.1
  have hhi : x ≤ (I.hi : ℝ) := hx.2
  have h := abs_le_max_abs_abs hlo hhi
  simpa [radius] using h

/-- Negation reverses the endpoints. -/
def neg (I : RatIvl) : RatIvl :=
  ⟨-I.hi, -I.lo, neg_le_neg I.lo_le_hi⟩

/-- Addition uses the sums of the corresponding endpoints. -/
def add (I J : RatIvl) : RatIvl :=
  ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.lo_le_hi J.lo_le_hi⟩

/-- Subtraction is addition with the reversed, negated second interval. -/
def sub (I J : RatIvl) : RatIvl :=
  ⟨I.lo - J.hi, I.hi - J.lo, sub_le_sub I.lo_le_hi J.lo_le_hi⟩

/-- A conservative product interval, symmetric about zero. -/
def mul (I J : RatIvl) : RatIvl :=
  ⟨-(I.radius * J.radius), I.radius * J.radius,
    neg_le_self (mul_nonneg I.radius_nonneg J.radius_nonneg)⟩

/-- A conservative natural-power interval, symmetric about zero. -/
def pow (I : RatIvl) (n : ℕ) : RatIvl :=
  ⟨-(I.radius ^ n), I.radius ^ n, neg_le_self (pow_nonneg I.radius_nonneg n)⟩

theorem zero_outside_cases (I : RatIvl) (h0 : 0 ∉ (I : Set ℝ)) :
    (I.hi : ℝ) < 0 ∨ 0 < (I.lo : ℝ) := by
  by_cases hlo : 0 ≤ (I.lo : ℝ)
  · right
    exact lt_of_le_of_ne hlo fun heq ↦
      h0 ⟨heq.ge, heq.le.trans (Rat.cast_le.mpr I.lo_le_hi)⟩
  · left
    have hlo' : (I.lo : ℝ) < 0 := lt_of_not_ge hlo
    by_contra hhi
    exact h0 ⟨hlo'.le, le_of_not_gt hhi⟩

/-- Reciprocal of an interval known not to contain zero. -/
def inv (I : RatIvl) (h0 : 0 ∉ (I : Set ℝ)) : RatIvl :=
  ⟨1 / I.hi, 1 / I.lo, by
    rcases zero_outside_cases I h0 with hneg | hpos
    · have hc : (I.hi : ℝ) < ((0 : ℚ) : ℝ) := by
        simpa only [Rat.cast_zero] using hneg
      have hneg' : I.hi < 0 := (Rat.cast_lt (K := ℝ)).mp hc
      exact one_div_le_one_div_of_neg_of_le hneg' I.lo_le_hi
    · have hc : ((0 : ℚ) : ℝ) < (I.lo : ℝ) := by
        simpa only [Rat.cast_zero] using hpos
      have hpos' : 0 < I.lo := (Rat.cast_lt (K := ℝ)).mp hc
      exact one_div_le_one_div_of_le hpos' I.lo_le_hi⟩

/-- Division is multiplication by the certified reciprocal interval. -/
def div (I J : RatIvl) (h0 : 0 ∉ (J : Set ℝ)) : RatIvl :=
  mul I (inv J h0)

theorem mem_neg {I : RatIvl} {x : ℝ} (hx : x ∈ (I : Set ℝ)) :
    -x ∈ (neg I : Set ℝ) := by
  simpa [neg, carrier] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem mem_add {I J : RatIvl} {x y : ℝ} (hx : x ∈ (I : Set ℝ))
    (hy : y ∈ (J : Set ℝ)) : x + y ∈ (add I J : Set ℝ) := by
  simpa [add, carrier] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem mem_sub {I J : RatIvl} {x y : ℝ} (hx : x ∈ (I : Set ℝ))
    (hy : y ∈ (J : Set ℝ)) : x - y ∈ (sub I J : Set ℝ) := by
  simpa [sub, carrier] using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

theorem mem_mul {I J : RatIvl} {x y : ℝ} (hx : x ∈ (I : Set ℝ))
    (hy : y ∈ (J : Set ℝ)) : x * y ∈ (mul I J : Set ℝ) := by
  have h : -((I.radius : ℝ) * (J.radius : ℝ)) ≤ x * y ∧
      x * y ≤ (I.radius : ℝ) * (J.radius : ℝ) := by
    rw [← abs_le, abs_mul]
    calc
      |x| * |y| ≤ (I.radius : ℝ) * |y| :=
        mul_le_mul_of_nonneg_right (abs_le_radius hx) (abs_nonneg _)
      _ ≤ (I.radius : ℝ) * (J.radius : ℝ) :=
        mul_le_mul_of_nonneg_left (abs_le_radius hy) (by simpa using I.radius_nonneg)
  simpa [mul, carrier] using h

theorem mem_pow {I : RatIvl} {x : ℝ} (hx : x ∈ (I : Set ℝ)) (n : ℕ) :
    x ^ n ∈ (pow I n : Set ℝ) := by
  have h : -((I.radius : ℝ) ^ n) ≤ x ^ n ∧ x ^ n ≤ (I.radius : ℝ) ^ n := by
    rw [← abs_le, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_radius hx) n
  have hcast : ((I.radius ^ n : ℚ) : ℝ) = (I.radius : ℝ) ^ n :=
    map_pow (Rat.castHom ℝ) I.radius n
  simpa [pow, carrier, hcast] using h

theorem mem_inv {I : RatIvl} {x : ℝ} (hx : x ∈ (I : Set ℝ))
    (h0 : 0 ∉ (I : Set ℝ)) : x⁻¹ ∈ (inv I h0 : Set ℝ) := by
  rcases zero_outside_cases I h0 with hneg | hpos
  · constructor
    · simpa [inv, carrier, one_div] using one_div_le_one_div_of_neg_of_le hneg hx.2
    · simpa [inv, carrier, one_div] using
        one_div_le_one_div_of_neg_of_le (lt_of_le_of_lt hx.2 hneg) hx.1
  · constructor
    · simpa [inv, carrier, one_div] using
        one_div_le_one_div_of_le (lt_of_lt_of_le hpos hx.1) hx.2
    · simpa [inv, carrier, one_div] using one_div_le_one_div_of_le hpos hx.1

theorem mem_div {I J : RatIvl} {x y : ℝ} (hx : x ∈ (I : Set ℝ))
    (hy : y ∈ (J : Set ℝ)) (h0 : 0 ∉ (J : Set ℝ)) :
    x / y ∈ (div I J h0 : Set ℝ) := by
  rw [div_eq_mul_inv]
  exact mem_mul hx (mem_inv hy h0)

end RatIvl

end Odlyzko.Interval
