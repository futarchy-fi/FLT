/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeCoordinateUnique
public import Mathlib.Data.ZMod.Basic

/-!
# Residue classes attached to nodal branches

The two strict branches receive k and -k modulo n. At the middle depth
these agree, so the label is independent of the tangent test there.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The signed depth, with the two signs identified at the middle component. -/
noncomputable def nodeBranchLabel (n k : ℕ) (b : R) : ZMod n := by
  classical
  exact if 2 * k = n ∨ b ∈ maximalIdeal R then (k : ZMod n) else -(k : ZMod n)

/-- Depth zero has label zero on both tangent branches. -/
@[simp] theorem nodeBranchLabel_zero (n : ℕ) (b : R) : nodeBranchLabel n 0 b = 0 := by
  classical
  simp [nodeBranchLabel]

/-- The first strict tangent branch has positive label. -/
theorem nodeBranchLabel_of_mem (n k : ℕ) {b : R} (hb : b ∈ maximalIdeal R) :
    nodeBranchLabel n k b = (k : ZMod n) := by
  classical
  simp [nodeBranchLabel, hb]

/-- The second strict tangent branch has negative label. -/
theorem nodeBranchLabel_of_unit {n k : ℕ} (hk : 2 * k ≠ n) {b : R} (hb : IsUnit b) :
    nodeBranchLabel n k b = -(k : ZMod n) := by
  classical
  simp [nodeBranchLabel, hk, show b ∉ maximalIdeal R from fun h => h hb]

/-- A middle-depth label is its own negative. -/
theorem nodeBranchLabel_middle {n k : ℕ} (hk : 2 * k = n) (b : R) :
    nodeBranchLabel n k b = (k : ZMod n) ∧ (k : ZMod n) = -(k : ZMod n) := by
  classical
  refine ⟨by simp [nodeBranchLabel, hk], ?_⟩
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← Nat.cast_add, ← two_mul, hk, ZMod.natCast_self]

/-- In the permitted depth range, label zero is equivalent to depth zero. -/
theorem nodeBranchLabel_eq_zero_iff {n k : ℕ} (hn : 0 < n) (hk : k ≤ n / 2) (b : R) :
    nodeBranchLabel n k b = 0 ↔ k = 0 := by
  classical
  have hlt : k < n := by omega
  have hc : (k : ZMod n) = 0 ↔ k = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨fun hd => Nat.eq_zero_of_dvd_of_lt hd hlt, fun h => h ▸ dvd_zero n⟩
  unfold nodeBranchLabel
  split_ifs <;> simpa only [neg_eq_zero] using hc

/-- Primitive factorization witnesses give the same branch label. -/
theorem nodeBranchLabel_factorization_independent [IsDomain R] {π a b c d : R}
    (hπ : π ≠ 0) (hgen : maximalIdeal R = Ideal.span {π}) (n : ℕ) {k l : ℕ}
    (hab : IsUnit a ∨ IsUnit b) (hcd : IsUnit c ∨ IsUnit d)
    (hx : π ^ k * a = π ^ l * c) (hy : π ^ k * b = π ^ l * d) :
    nodeBranchLabel n k b = nodeBranchLabel n l d := by
  obtain ⟨rfl, _, rfl⟩ := node_primitive_coordinates_unique hπ hgen hab hcd hx hy
  rfl

end FLT.Mazur
