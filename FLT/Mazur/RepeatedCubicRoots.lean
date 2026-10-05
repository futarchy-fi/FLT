/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CubicComponentBound

/-!
# Rational repeated roots of a monic cubic

A specified repeated root factors the cubic in every characteristic. The
remaining linear factor separates the double-root and triple-root cases,
without assuming that the residue field is perfect.
-/

@[expose] public section

namespace FLT.Mazur

/-- Factor a monic cubic at a root where its derivative vanishes. -/
theorem monicCubic_factor_at_repeated_root {R : Type*} [CommRing R] {b c d t : R}
    (ht : t ^ 3 + b * t ^ 2 + c * t + d = 0)
    (hd : 3 * t ^ 2 + 2 * b * t + c = 0) (z : R) :
    z ^ 3 + b * z ^ 2 + c * z + d = (z - t) ^ 2 * (z + b + 2 * t) := by
  linear_combination ht + (z - t) * hd

/-- Every root is the specified repeated root or the remaining linear root. -/
theorem monicCubic_roots_of_repeated {F : Type*} [Field F] {b c d t z : F}
    (ht : t ^ 3 + b * t ^ 2 + c * t + d = 0)
    (hd : 3 * t ^ 2 + 2 * b * t + c = 0) :
    z ^ 3 + b * z ^ 2 + c * z + d = 0 ↔ z = t ∨ z = -b - 2 * t := by
  rw [monicCubic_factor_at_repeated_root ht hd, mul_eq_zero, pow_eq_zero_iff (by decide)]
  constructor
  · rintro (h | h)
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      linear_combination h
  · rintro (rfl | rfl)
    · exact Or.inl (sub_self _)
    · right
      ring

/-- The other root is simple precisely when the specified root is not triple. -/
theorem monicCubic_other_root_derivative {R : Type*} [CommRing R] {b c t : R}
    (hd : 3 * t ^ 2 + 2 * b * t + c = 0) :
    3 * (-b - 2 * t) ^ 2 + 2 * b * (-b - 2 * t) + c = (b + 3 * t) ^ 2 := by
  linear_combination hd

/-- A monic cubic has at most one rational repeated root, also in characteristic three. -/
theorem monicCubic_repeated_root_unique {F : Type*} [Field F] {b c d t z : F}
    (ht : t ^ 3 + b * t ^ 2 + c * t + d = 0)
    (hd : 3 * t ^ 2 + 2 * b * t + c = 0)
    (hz : z ^ 3 + b * z ^ 2 + c * z + d = 0)
    (he : 3 * z ^ 2 + 2 * b * z + c = 0) : z = t := by
  rcases (monicCubic_roots_of_repeated ht hd).mp hz with h | rfl
  · exact h
  · rw [monicCubic_other_root_derivative hd] at he
    have h := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp he
    linear_combination -h

/-- Vanishing of the remaining root separation gives the triple-root factorization. -/
theorem monicCubic_triple_root_factor {R : Type*} [CommRing R] {b c d t : R}
    (ht : t ^ 3 + b * t ^ 2 + c * t + d = 0)
    (hd : 3 * t ^ 2 + 2 * b * t + c = 0) (hb : b + 3 * t = 0) (z : R) :
    z ^ 3 + b * z ^ 2 + c * z + d = (z - t) ^ 3 := by
  rw [monicCubic_factor_at_repeated_root ht hd]
  linear_combination (z - t) ^ 2 * hb

end FLT.Mazur
