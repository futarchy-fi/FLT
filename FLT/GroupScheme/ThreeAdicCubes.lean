/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The three-adic cube obstruction for parameters supported at two and three

Reduction modulo nine excludes `2` and `4` as three-adic cubes. Together
with the three-adic valuation, this detects the trivial class among the
nine representatives `2 ^ i * 3 ^ j`, for `0 ≤ i, j < 3`.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- The only cube residues modulo nine are zero, one, and minus one. -/
theorem cube_mod_nine (x : ZMod 9) : x ^ 3 = 0 ∨ x ^ 3 = 1 ∨ x ^ 3 = -1 := by
  revert x
  decide

/-- Of the reduced powers of two, only one is a cube modulo nine. -/
theorem pow_two_cube_mod_nine (i : Fin 3) (x : ZMod 9)
    (h : x ^ 3 = 2 ^ (i : ℕ)) : i = 0 := by
  revert h
  revert x i
  decide

/-- A cube root of an integral three-adic number is itself integral. -/
theorem exists_integral_cube_root {a : ℤ_[3]} {x : ℚ_[3]}
    (h : x ^ 3 = (a : ℚ_[3])) : ∃ y : ℤ_[3], y ^ 3 = a := by
  have hx : ‖x‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg x) (by decide : 3 ≠ 0)).mp
    (by rw [← norm_pow, h]; exact a.2)
  refine ⟨⟨x, hx⟩, PadicInt.ext ?_⟩
  exact h

/-- A reduced power of two that is a cube over `ℚ₃` has exponent zero. -/
theorem pow_two_cube_three_adic (i : Fin 3) {x : ℚ_[3]}
    (h : x ^ 3 = 2 ^ (i : ℕ)) : i = 0 := by
  have h' : x ^ 3 = ((2 ^ (i : ℕ) : ℤ_[3]) : ℚ_[3]) := by
    exact_mod_cast h
  obtain ⟨y, hy⟩ := exists_integral_cube_root h'
  apply pow_two_cube_mod_nine i (PadicInt.toZModPow 2 y)
  simpa only [map_pow, map_ofNat] using congrArg (PadicInt.toZModPow 2) hy

/-- The valuation of a parameter supported at two and three reads off the
exponent of three, also for negative exponents. -/
theorem valuation_two_three (i j : ℤ) :
    Padic.valuation ((2 : ℚ_[3]) ^ i * 3 ^ j) = j := by
  rw [Padic.valuation_mul (zpow_ne_zero _ (by norm_num))
    (zpow_ne_zero _ (by norm_num)), Padic.valuation_zpow, Padic.valuation_zpow]
  norm_num [padicValNat.eq_zero_of_not_dvd]

/-- A reduced parameter supported at two and three is a three-adic cube
exactly when both exponents vanish. -/
theorem reduced_two_three_cube_iff (i j : Fin 3) :
    (∃ x : ℚ_[3], x ^ 3 = 2 ^ (i : ℕ) * 3 ^ (j : ℕ)) ↔ i = 0 ∧ j = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    have hv := congrArg Padic.valuation hx
    rw [Padic.valuation_pow] at hv
    have hr : Padic.valuation ((2 : ℚ_[3]) ^ (i : ℕ) * 3 ^ (j : ℕ)) = (j : ℕ) := by
      exact_mod_cast valuation_two_three (i : ℕ) (j : ℕ)
    rw [hr] at hv
    have hj : j = 0 := by
      apply Fin.ext
      have := j.isLt
      simp only [Fin.val_zero]
      omega
    subst j
    exact ⟨pow_two_cube_three_adic i (by simpa using hx), rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, by norm_num⟩

end ThreeAdicPlan
