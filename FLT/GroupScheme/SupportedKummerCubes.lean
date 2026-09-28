/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ThreeAdicCubes
public import Mathlib.Tactic.Ring

/-!
# Local detection of rational cube classes supported at two and three

A rational number represented modulo cubes by powers of two and three
is a rational cube if it is a cube over `ℚ₃`. The exponents may be negative;
the rational cube factor also absorbs the sign.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- Multiplying by a nonzero cube preserves the existence of a cube root. -/
theorem exists_cube_mul_cube_iff {K : Type*} [Field K] (a b : K) (hb : b ≠ 0) :
    (∃ x : K, x ^ 3 = a * b ^ 3) ↔ ∃ x : K, x ^ 3 = a := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x / b, ?_⟩
    rw [div_pow, hx, mul_div_cancel_right₀ _ (pow_ne_zero _ hb)]
  · rintro ⟨x, hx⟩
    exact ⟨x * b, by rw [mul_pow, hx]⟩

/-- Euclidean division of an exponent separates a reduced exponent from a cube. -/
theorem zpow_mod_three_mul_cube {K : Type*} [Field K] (a : K) (ha : a ≠ 0) (i : ℤ) :
    a ^ i = a ^ (i % 3) * (a ^ (i / 3)) ^ 3 := by
  rw [← zpow_natCast (a ^ (i / 3)) 3, ← zpow_mul, ← zpow_add₀ ha]
  congr 1
  omega

/-- The exponent remainder modulo three, regarded as one of the three reduced exponents. -/
def cubeExponentRemainder (i : ℤ) : Fin 3 :=
  ⟨(i % 3).toNat, by omega⟩

/-- The finite exponent remainder agrees with the integer remainder. -/
theorem cubeExponentRemainder_coe (i : ℤ) :
    ((cubeExponentRemainder i : ℕ) : ℤ) = i % 3 := by
  simp only [cubeExponentRemainder]
  omega

/-- Simultaneously reduce the two exponents modulo three, extracting an explicit cube. -/
theorem two_three_zpow_mod_cube {K : Type*} [Field K] [CharZero K] (i j : ℤ) :
    (2 : K) ^ i * 3 ^ j =
      (2 ^ (cubeExponentRemainder i : ℕ) * 3 ^ (cubeExponentRemainder j : ℕ)) *
        (2 ^ (i / 3) * 3 ^ (j / 3)) ^ 3 := by
  rw [zpow_mod_three_mul_cube (2 : K) (by norm_num) i,
    zpow_mod_three_mul_cube (3 : K) (by norm_num) j]
  rw [← cubeExponentRemainder_coe i, ← cubeExponentRemainder_coe j]
  simp only [zpow_natCast, mul_pow]
  ring

/-- A parameter supported at two and three is a three-adic cube precisely
when its two integer exponents are divisible by three. -/
theorem two_three_zpow_cube_iff (i j : ℤ) :
    (∃ x : ℚ_[3], x ^ 3 = 2 ^ i * 3 ^ j) ↔ 3 ∣ i ∧ 3 ∣ j := by
  rw [two_three_zpow_mod_cube, exists_cube_mul_cube_iff _ _
    (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (by norm_num))),
    reduced_two_three_cube_iff]
  simp only [Fin.ext_iff, cubeExponentRemainder, Fin.val_zero, Int.dvd_iff_emod_eq_zero]
  omega

/-- For a rational representative supported at two and three modulo cubes,
three-adic cubeness implies rational cubeness. No ramification or extension-class
comparison is assumed to have constructed this representative. -/
theorem rational_cube_of_supported_three_adic_cube (a b : ℚ) (hb : b ≠ 0) (i j : ℤ)
    (ha : a = (2 ^ i * 3 ^ j) * b ^ 3)
    (hlocal : ∃ x : ℚ_[3], x ^ 3 = (a : ℚ_[3])) :
    ∃ r : ℚ, r ^ 3 = a := by
  have hb' : (b : ℚ_[3]) ≠ 0 := by exact_mod_cast hb
  have hlocal' : ∃ x : ℚ_[3], x ^ 3 =
      ((2 : ℚ_[3]) ^ i * 3 ^ j) * (b : ℚ_[3]) ^ 3 := by
    simpa only [ha, Rat.cast_mul, Rat.cast_pow, Rat.cast_zpow, Rat.cast_ofNat] using hlocal
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := (two_three_zpow_cube_iff i j).mp
    ((exists_cube_mul_cube_iff _ _ hb').mp hlocal')
  refine ⟨(2 ^ m * 3 ^ n) * b, ?_⟩
  rw [ha, hm, hn, mul_pow, mul_pow]
  congr 1
  simp only [mul_comm (3 : ℤ), zpow_mul, zpow_ofNat]

end ThreeAdicPlan
