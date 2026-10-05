/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelAdditivity
public import FLT.Mazur.EllipticNodeLabelDecode

/-!
# Exact depth and branch of same-branch sums

For first-branch depths k and j the sum has depth k+j up to the midpoint,
and depth n-k-j on the second branch beyond it. The statements include
equal depths and doubling and apply to every primitive coordinate witness.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Before or at the midpoint, first-branch depths add without wrapping. -/
theorem NodePointCoordinates.add_first_depth_le_middle
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hk : 0 < v.depth + w.depth) (hkn : 2 * (v.depth + w.depth) ≤ n)
    (hun : u.depth ≤ n / 2) (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    u.depth = v.depth + w.depth ∧
      (2 * (v.depth + w.depth) = n ∨ u.b ∈ maximalIdeal A) := by
  have he := nodePointLabel_add D P Q
  rw [nodePointLabel_eq_of_coordinates D u, nodePointLabel_eq_of_coordinates D v,
    nodePointLabel_eq_of_coordinates D w, nodeBranchLabel_of_mem n v.depth hb,
    nodeBranchLabel_of_mem n w.depth hd, ← Nat.cast_add] at he
  exact nodeBranchLabel_decode_positive D.depth_pos hk (by omega) hun u.b he

/-- Beyond the midpoint, first-branch depths wrap onto the second branch. -/
theorem NodePointCoordinates.add_first_depth_gt_middle
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hkn : n < 2 * (v.depth + w.depth)) (hvn : 2 * v.depth < n) (hwn : 2 * w.depth < n)
    (hun : u.depth ≤ n / 2) (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    u.depth = n - (v.depth + w.depth) ∧ IsUnit u.b := by
  have he := nodePointLabel_add D P Q
  rw [nodePointLabel_eq_of_coordinates D u, nodePointLabel_eq_of_coordinates D v,
    nodePointLabel_eq_of_coordinates D w, nodeBranchLabel_of_mem n v.depth hb,
    nodeBranchLabel_of_mem n w.depth hd, ← Nat.cast_add] at he
  have hc : ((v.depth + w.depth : ℕ) : ZMod n) = -((n - (v.depth + w.depth) : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : v.depth + w.depth ≤ n), ZMod.natCast_self, zero_sub, neg_neg]
  exact nodeBranchLabel_decode_negative D.depth_pos (by omega) (by omega) hun u.b (he.trans hc)

end FLT.Mazur
