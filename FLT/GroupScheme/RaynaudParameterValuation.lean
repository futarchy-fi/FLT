/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic

/-!
# Binary valuations of unramified Raynaud parameters

A pair of integral parameters whose product is p times a unit has valuations
zero and one, in some order. This is the scalar calculation in Raynaud,
*Schémas en groupes de type (p,...,p)*, §3.3(2), for the base ℤ_p.
It does not construct presentations or extend them over an unramified base.
-/

@[expose] public section

namespace RaynaudParameters

variable {p : ℕ} [Fact p.Prime]

/-- A p-adic unit has valuation zero, as follows by multiplying by its inverse. -/
theorem valuation_unit (u : ℤ_[p]ˣ) : PadicInt.valuation (u : ℤ_[p]) = 0 := by
  have h := congrArg PadicInt.valuation (Units.mul_inv u)
  rw [PadicInt.valuation_mul u.ne_zero (Units.ne_zero _), PadicInt.valuation_one] at h
  omega

/-- Both factors of p times a unit are nonzero. -/
theorem parameters_ne_zero {a b : ℤ_[p]} (u : ℤ_[p]ˣ)
    (h : a * b = (p : ℤ_[p]) * u) : a ≠ 0 ∧ b ≠ 0 := by
  have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  exact mul_ne_zero_iff.mp (h ▸ mul_ne_zero hp u.ne_zero)

/-- The unramified parameter relation gives complementary valuations. -/
theorem valuation_pair {a b : ℤ_[p]} (u : ℤ_[p]ˣ)
    (h : a * b = (p : ℤ_[p]) * u) :
    a.valuation + b.valuation = 1 := by
  obtain ⟨ha, hb⟩ := parameters_ne_zero u h
  have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hv := congrArg PadicInt.valuation h
  simpa only [PadicInt.valuation_mul ha hb, PadicInt.valuation_mul hp u.ne_zero,
    PadicInt.valuation_p, valuation_unit, add_zero] using hv

/-- Unramified parameter valuations are the complementary binary digits. -/
theorem valuation_digits {a b : ℤ_[p]} (u : ℤ_[p]ˣ)
    (h : a * b = (p : ℤ_[p]) * u) :
    (a.valuation = 0 ∧ b.valuation = 1) ∨
    (a.valuation = 1 ∧ b.valuation = 0) := by
  have := valuation_pair u h
  omega

end RaynaudParameters
