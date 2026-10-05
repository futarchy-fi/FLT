/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDifferenceLabels

/-!
# Recovering primitive depth and branch from a label

A positive label in the half interval determines the depth and first branch,
with the usual midpoint exception. A negative strict label determines the
same absolute depth and the second branch.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Decode a positive label, allowing the midpoint where the tangent test is immaterial. -/
theorem nodeBranchLabel_decode_positive {n k r : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hkn : k ≤ n / 2) (hrn : r ≤ n / 2) (b : R)
    (he : nodeBranchLabel n r b = (k : ZMod n)) :
    r = k ∧ (2 * k = n ∨ b ∈ maximalIdeal R) := by
  have hd : r = k := nodeBranchLabel_eq_imp_depth hn hrn hkn b (0 : R)
    (he.trans (nodeBranchLabel_of_mem n k (Ideal.zero_mem _)).symm)
  refine ⟨hd, ?_⟩
  by_cases hm : 2 * k = n
  · exact Or.inl hm
  · right
    by_contra hb
    have hu : IsUnit b := not_not.mp hb
    rw [hd, nodeBranchLabel_of_unit hm hu] at he
    exact node_depth_cast_ne_neg hk (by omega) he.symm

/-- Decode a negative strict label into its depth and unit second coordinate. -/
theorem nodeBranchLabel_decode_negative {n k r : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hkn : 2 * k < n) (hrn : r ≤ n / 2) (b : R)
    (he : nodeBranchLabel n r b = -(k : ZMod n)) : r = k ∧ IsUnit b := by
  have hd : r = k := nodeBranchLabel_eq_imp_depth hn hrn (by omega) b (1 : R)
    (he.trans (nodeBranchLabel_eq_neg_of_unit n k isUnit_one).symm)
  refine ⟨hd, ?_⟩
  by_contra hb
  have hm : b ∈ maximalIdeal R := hb
  rw [hd, nodeBranchLabel_of_mem n k hm] at he
  exact node_depth_cast_ne_neg hk hkn he

end FLT.Mazur
