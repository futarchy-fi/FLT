/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeBranchLabel

/-!
# Signed depth separation

Within the interval from zero to n/2, equality of signed residues forces
equality of absolute depths. At a positive strict depth the two signs are
distinct, so opposite labels detect opposite tangent branches.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

/-- Opposite residues in the half interval have the same absolute depth. -/
theorem node_depth_eq_of_cast_eq_neg {n k l : ℕ} (hk : k ≤ n / 2) (hl : l ≤ n / 2)
    (he : (k : ZMod n) = -(l : ZMod n)) : k = l := by
  have hz : ((k + l : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_add, he, neg_add_cancel]
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  by_cases h0 : k + l = 0
  · omega
  · have hn := Nat.le_of_dvd (by omega : 0 < k + l) hd
    omega

/-- A positive strict depth is distinct from its negative residue. -/
theorem node_depth_cast_ne_neg {n k : ℕ} (hk : 0 < k) (hkn : 2 * k < n) :
    (k : ZMod n) ≠ -(k : ZMod n) := by
  intro he
  have hz : ((2 * k : ℕ) : ZMod n) = 0 := by
    rw [two_mul, Nat.cast_add]
    exact eq_neg_iff_add_eq_zero.mp he
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hn := Nat.le_of_dvd (by omega : 0 < 2 * k) hd
  omega

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Equal branch labels determine the common depth throughout the allowed interval. -/
theorem nodeBranchLabel_eq_imp_depth {n k l : ℕ} (hn : 0 < n)
    (hk : k ≤ n / 2) (hl : l ≤ n / 2) (b d : R)
    (he : nodeBranchLabel n k b = nodeBranchLabel n l d) : k = l := by
  classical
  have hsame (he : (k : ZMod n) = (l : ZMod n)) : k = l := by
    have hm := (ZMod.natCast_eq_natCast_iff' k l n).mp he
    simpa only [Nat.mod_eq_of_lt (by omega : k < n),
      Nat.mod_eq_of_lt (by omega : l < n)] using hm
  unfold nodeBranchLabel at he
  split_ifs at he with hb hd hd
  · exact hsame he
  · exact node_depth_eq_of_cast_eq_neg hk hl he
  · exact node_depth_eq_of_cast_eq_neg hk hl (neg_eq_iff_eq_neg.mp he)
  · exact hsame (neg_injective he)

/-- At strict positive depth, opposite labels mean opposite tangent tests. -/
theorem nodeBranchLabel_opposite_iff {n k : ℕ} (hk : 0 < k) (hkn : 2 * k < n)
    (b d : R) :
    nodeBranchLabel n k d = -nodeBranchLabel n k b ↔
      (b ∈ maximalIdeal R ∧ IsUnit d) ∨ (IsUnit b ∧ d ∈ maximalIdeal R) := by
  classical
  have hne := node_depth_cast_ne_neg hk hkn
  have hm : 2 * k ≠ n := by omega
  have hbunit : b ∉ maximalIdeal R ↔ IsUnit b := not_not
  have hdunit : d ∉ maximalIdeal R ↔ IsUnit d := not_not
  by_cases hb : b ∈ maximalIdeal R <;> by_cases hd : d ∈ maximalIdeal R
  · simp [nodeBranchLabel, hm, hb, hd, hne, show ¬IsUnit b from hb,
      show ¬IsUnit d from hd]
  · simp [nodeBranchLabel, hm, hb, hd, hdunit.mp hd]
  · simp [nodeBranchLabel, hm, hb, hd, hbunit.mp hb]
  · simp [nodeBranchLabel, hm, hb, hd, Ne.symm hne]

end FLT.Mazur
