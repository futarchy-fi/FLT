/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeFirstTriple
public import FLT.Mazur.EllipticNodeMixedLabels
public import FLT.Mazur.EllipticNodeSameBranchAddition
public import FLT.Mazur.EllipticNodeUnequalDepthAddition

/-!
# Label addition for two first-branch points

The sum is singular. If it stays on the first branch or reaches the midpoint,
apply the already proved mixed-branch law after subtracting an input. If it
lands on the second branch, the first-branch triple-depth identity gives the
wraparound relation. Doubling is included.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Any witness of a singular point has positive depth. -/
theorem NodePointCoordinates.depth_pos_of_not_smooth
    (v : NodePointCoordinates A W π P) (h : ¬ SmoothReduction A W P) : 0 < v.depth := by
  by_contra hn
  apply h
  apply (nodePointLabel_eq_zero_iff D P).mp
  rw [nodePointLabel_eq_of_coordinates D v, show v.depth = 0 by omega, nodeBranchLabel_zero]

/-- Ordered first-branch summands satisfy label addition, including doubling and wraparound. -/
theorem nodePointLabel_add_first_first_le
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkw : v.depth ≤ w.depth) (hw : 2 * w.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  have hs : ¬ SmoothReduction A W (P + Q) := by
    rcases eq_or_lt_of_le hkw with he | he
    · exact v.not_smooth_add_of_first_branch D w hk (by omega) he hb hd
    · exact v.not_smooth_add D w hk he (by omega)
  obtain ⟨r, hr⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem (P + Q) hs
  have hr0 := r.depth_pos_of_not_smooth D hs
  obtain ⟨w', hw', hwl⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  rw [hw'] at hwl
  have hw'b : IsUnit w'.b := by
    rcases (nodeBranchLabel_opposite_iff (by omega) hw w.b w'.b).mp hwl with h | h
    · exact h.2
    · exact (hd h.1).elim
  by_cases hmid : 2 * r.depth = n
  · have he := nodePointLabel_add_shallower_middle D w' r (by omega) (by omega) hmid
    have hcancel : -Q + (P + Q) = P := by abel
    rw [hcancel, nodePointLabel_neg] at he
    linear_combination -he
  by_cases hrb : r.b ∈ maximalIdeal A
  · have he := nodePointLabel_add_first_unit D r w' hr0 (by omega) hr (by omega) hrb hw'b
    have hcancel : (P + Q) + -Q = P := by abel
    rw [hcancel, nodePointLabel_neg] at he
    linear_combination -he
  · have hrbu : IsUnit r.b := not_not.mp hrb
    obtain ⟨u, hu, hul⟩ := exists_nodePointCoordinates_inverse D r hr
    rw [hu] at hul
    have hub : u.b ∈ maximalIdeal A := by
      rcases (nodeBranchLabel_opposite_iff hr0 (by omega) r.b u.b).mp hul with h | h
      · exact (h.1 hrbu).elim
      · exact h.2
    have he := node_depth_sum_of_first_triple D v w u hk hkw hw (by omega) (by omega) hb hd hub
    have heZ : (v.depth : ZMod n) + (w.depth : ZMod n) + (r.depth : ZMod n) = 0 := by
      rw [hu] at he
      simpa only [Nat.cast_add, ZMod.natCast_self] using congrArg (fun k : ℕ => (k : ZMod n)) he
    rw [nodePointLabel_eq_of_coordinates D r, nodePointLabel_eq_of_coordinates D v,
      nodePointLabel_eq_of_coordinates D w, nodeBranchLabel_eq_neg_of_unit n r.depth hrbu,
      nodeBranchLabel_of_mem n v.depth hb, nodeBranchLabel_of_mem n w.depth hd]
    linear_combination -heZ

/-- Two first-branch points satisfy label addition without an ordering of their depths. -/
theorem nodePointLabel_add_first_first
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 0 < v.depth) (hw : 0 < w.depth) (hvn : 2 * v.depth < n) (hwn : 2 * w.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  rcases le_total v.depth w.depth with h | h
  · exact nodePointLabel_add_first_first_le D v w hv h hwn hb hd
  · simpa only [add_comm] using nodePointLabel_add_first_first_le D w v hw h hvn hd hb

end FLT.Mazur
