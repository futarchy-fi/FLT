/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NilpotentTorsionPowerEquality
public import Mathlib.RingTheory.Localization.Basic

/-!
# Integer localization detects the torsion obstruction to equalizing powers

Localizing at positive integer scalars detects exactly the differences killed
by a positive integer. Combined with nilpotence, this produces a positive
power equality in the original ring, including its mixed-characteristic data.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PositiveIntegerLocalization
universe u
variable (R : Type u) [CommRing R]

/-- The multiplicative system of positive integer scalars, allowing torsion in the ring. -/
def scalars : Submonoid R where
  carrier := {r | ∃ m : ℕ, 0 < m ∧ (m : R) = r}
  one_mem' := ⟨1, Nat.one_pos, Nat.cast_one⟩
  mul_mem' := by
    rintro a b ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
    exact ⟨m * n, Nat.mul_pos hm hn, Nat.cast_mul _ _⟩

/-- Inverting positive integer scalars in the original ring. -/
abbrev Rationalized := Localization (scalars R)

/-- Vanishing after integer localization is exactly positive-integer torsion. -/
theorem map_eq_zero_iff (x : R) :
    algebraMap R (Rationalized R) x = 0 ↔ ∃ m : ℕ, 0 < m ∧ (m : R) * x = 0 := by
  rw [IsLocalization.map_eq_zero_iff (scalars R)]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨m, hm, he⟩ := s.property
    exact ⟨m, hm, he.symm ▸ hs⟩
  · rintro ⟨m, hm, he⟩
    exact ⟨⟨(m : R), m, hm, rfl⟩, he⟩

/-- Equality after integer localization detects torsion of the original difference. -/
theorem map_eq_iff (x y : R) :
    algebraMap R (Rationalized R) x = algebraMap R (Rationalized R) y ↔
      ∃ m : ℕ, 0 < m ∧ (m : R) * (x - y) = 0 := by
  rw [← sub_eq_zero, ← map_sub, map_eq_zero_iff]

/-- A nilpotent discrepancy vanishing rationally is removed by a positive power. -/
theorem exists_pos_pow_eq {x y : R} (hnil : IsNilpotent (x - y))
    (h : algebraMap R (Rationalized R) x = algebraMap R (Rationalized R) y) :
    ∃ e : ℕ, 0 < e ∧ x ^ e = y ^ e := by
  obtain ⟨m, hm, hkill⟩ := (map_eq_iff R x y).mp h
  exact NilpotentTorsionPowerEquality.exists_pos_pow_eq hm hnil hkill

/-- Reducedness after integer localization suffices for every nilpotent discrepancy. -/
theorem exists_pos_pow_eq_of_reduced [IsReduced (Rationalized R)]
    {x y : R} (hnil : IsNilpotent (x - y)) : ∃ e : ℕ, 0 < e ∧ x ^ e = y ^ e := by
  apply exists_pos_pow_eq R hnil
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (hnil.map (algebraMap R (Rationalized R))).eq_zero

end FLT.Mazur.PositiveIntegerLocalization
