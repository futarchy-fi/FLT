/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A marking-denominator localization retains the entire node socle

The denominator acts as the identity on every element annihilated by both
node coordinates. Consequently localization detects zero on that full socle,
without a reducedness assumption or removal of nilpotents.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodeSocleLocalization
variable {R : Type*} [CommRing R] (x y z : R)

/-- The actual marking denominator acts identically on the full common annihilator. -/
theorem denominator_mul (hx : x * z = 0) (hy : y * z = 0) :
    ((1 - x) * (1 - y)) * z = z := by
  rw [mul_assoc, sub_mul 1 y z, one_mul, hy, sub_zero, sub_mul, one_mul, hx, sub_zero]

/-- Every denominator power still acts identically on each node-socle element. -/
theorem denominator_pow_mul (hx : x * z = 0) (hy : y * z = 0) (n : ℕ) :
    ((1 - x) * (1 - y)) ^ n * z = z := by
  induction n with
  | zero => rw [pow_zero, one_mul]
  | succ n ih => rw [pow_succ, mul_assoc, denominator_mul x y z hx hy, ih]

/-- The explicit denominator localization loses no element of the full common annihilator. -/
theorem eq_zero_of_localization (hx : x * z = 0) (hy : y * z = 0)
    (hz : algebraMap R (Localization.Away ((1 - x) * (1 - y))) z = 0) : z = 0 := by
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers ((1 - x) * (1 - y))) _ z).mp hz
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, denominator_pow_mul x y z hx hy n] at hs
  exact hs

/-- Vanishing of the localized original socle is equivalent to its original vanishing. -/
theorem socle_vanishes_iff :
    (∀ z : R, x * z = 0 → y * z = 0 → z = 0) ↔
      ∀ z : R, x * z = 0 → y * z = 0 →
        algebraMap R (Localization.Away ((1 - x) * (1 - y))) z = 0 := by
  constructor
  · intro h z hx hy
    rw [h z hx hy, map_zero]
  · intro h z hx hy
    exact eq_zero_of_localization x y z hx hy (h z hx hy)

end FLT.Mazur.NodeSocleLocalization
