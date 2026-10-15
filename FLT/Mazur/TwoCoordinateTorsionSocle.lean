/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# A nonzero two-coordinate torsion ideal has a nonzero node socle

Repeated multiplication lowers a finite annihilation exponent until a
nonzero element is killed by both coordinates. No Noetherian or reduced
hypothesis is required, and all elements stay in the original ideal.
-/

@[expose] public section
namespace FLT.Mazur.TwoCoordinateTorsionSocle
variable {R : Type*} [CommRing R]

/-- A finite power annihilator supplies a nonzero last multiple. -/
theorem last_nonzero (a z : R) (hz : z ≠ 0) {k : ℕ} (hk : a ^ k * z = 0) :
    ∃ j : ℕ, a ^ j * z ≠ 0 ∧ a * (a ^ j * z) = 0 := by
  induction k generalizing z with
  | zero => exact False.elim (hz (by simpa only [pow_zero, one_mul] using hk))
  | succ k ih =>
    by_cases ha : a * z = 0
    · exact ⟨0, by simpa only [pow_zero, one_mul] using hz,
        by simpa only [pow_zero, one_mul] using ha⟩
    · have he : a ^ k * (a * z) = 0 := by
        simpa only [pow_succ, mul_assoc] using hk
      obtain ⟨j, hj, hj'⟩ := ih (a * z) ha he
      exact ⟨j + 1, by simpa only [pow_succ, mul_assoc] using hj,
        by simpa only [pow_succ, mul_assoc] using hj'⟩

/-- Nonzero torsion for both coordinates produces a nonzero element killed by each. -/
theorem exists_common_annihilator (I : Ideal R) (x y z : R) (hz : z ∈ I) (hn : z ≠ 0)
    {a b : ℕ} (hx : x ^ a * z = 0) (hy : y ^ b * z = 0) :
    ∃ w : R, w ∈ I ∧ w ≠ 0 ∧ x * w = 0 ∧ y * w = 0 := by
  obtain ⟨i, hi, hi'⟩ := last_nonzero x z hn hx
  have hey : y ^ b * (x ^ i * z) = 0 := by
    rw [mul_left_comm, hy, mul_zero]
  obtain ⟨j, hj, hj'⟩ := last_nonzero y (x ^ i * z) hi hey
  refine ⟨y ^ j * (x ^ i * z), I.mul_mem_left _ (I.mul_mem_left _ hz), hj, ?_, hj'⟩
  rw [mul_left_comm, hi', mul_zero]

/-- For a coordinate-torsion ideal, vanishing is exactly absence of a nonzero node socle. -/
theorem eq_bot_iff (I : Ideal R) (x y : R)
    (ht : ∀ z ∈ I, ∃ a b : ℕ, x ^ a * z = 0 ∧ y ^ b * z = 0) :
    I = ⊥ ↔ ∀ z ∈ I, x * z = 0 → y * z = 0 → z = 0 := by
  constructor
  · intro he z hz _ _
    simpa only [he, Ideal.mem_bot] using hz
  · intro hs
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    by_contra hn
    obtain ⟨a, b, ha, hb⟩ := ht z hz
    obtain ⟨w, hw, hnw, hx, hy⟩ := exists_common_annihilator I x y z hz hn ha hb
    exact hnw (hs w hw hx hy)

end FLT.Mazur.TwoCoordinateTorsionSocle
