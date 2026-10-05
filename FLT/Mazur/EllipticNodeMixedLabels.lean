/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDifferenceLabels
public import FLT.Mazur.EllipticNodeOppositeLabels

/-!
# Label addition on opposite branches and at the midpoint

Negation supplies the reflected unequal-depth calculation. This proves the
label law for every pair on distinct strict branches, and for a midpoint
point plus any shallower singular point. Same-branch strict sums remain open.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- A shallower second-branch point and a deeper first-branch point satisfy label addition. -/
theorem nodePointLabel_add_of_unit_first_lt
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : IsUnit v.b) (hd : w.b ∈ maximalIdeal A) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  have hwstrict : 2 * w.depth < n := by
    have hne : 2 * w.depth ≠ n := fun h => hd (w.units_of_middle D h).1
    omega
  obtain ⟨v', hv', hvl⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', hwl⟩ := exists_nodePointCoordinates_inverse D w hw
  rw [hv'] at hvl
  rw [hw'] at hwl
  have hvb : v'.b ∈ maximalIdeal A := by
    rcases (nodeBranchLabel_opposite_iff hk (by omega) v.b v'.b).mp hvl with h | h
    · exact (h.1 hb).elim
    · exact h.2
  have hwb : IsUnit w'.b := by
    rcases (nodeBranchLabel_opposite_iff (by omega) hwstrict w.b w'.b).mp hwl with h | h
    · exact h.2
    · exact (hd h.1).elim
  have hs := nodePointLabel_add_of_first_unit D v' w' (by omega) (by omega)
    (by omega) hvb hwb
  rw [← neg_add, nodePointLabel_neg, nodePointLabel_neg, nodePointLabel_neg, ← neg_add] at hs
  exact neg_injective hs

/-- All depths are allowed when the first input is on the first branch and the second is a unit. -/
theorem nodePointLabel_add_first_unit
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 0 < v.depth) (hw : 0 < w.depth) (hvn : v.depth ≤ n / 2) (hwn : w.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  rcases lt_trichotomy v.depth w.depth with h | h | h
  · exact nodePointLabel_add_of_first_unit D v w hv h hwn hb hd
  · have hne : 2 * v.depth ≠ n := fun hm => hb (v.units_of_middle D hm).1
    exact nodePointLabel_add_of_opposite D v w hv (by omega) h hb hd
  · simpa only [add_comm] using nodePointLabel_add_of_unit_first_lt D w v hw h hvn hd hb

/-- Opposite tangent branches satisfy the label addition law, in either order. -/
theorem nodePointLabel_add_of_distinct_branches
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 0 < v.depth) (hw : 0 < w.depth) (hvn : v.depth ≤ n / 2) (hwn : w.depth ≤ n / 2)
    (hb : (v.b ∈ maximalIdeal A ∧ IsUnit w.b) ∨ (IsUnit v.b ∧ w.b ∈ maximalIdeal A)) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  rcases hb with ⟨hb, hd⟩ | ⟨hb, hd⟩
  · exact nodePointLabel_add_first_unit D v w hv hw hvn hwn hb hd
  · simpa only [add_comm] using nodePointLabel_add_first_unit D w v hw hv hwn hvn hd hb

/-- A midpoint point adds correctly to either strict branch at every smaller positive depth. -/
theorem nodePointLabel_add_shallower_middle
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hm : 2 * w.depth = n) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  by_cases hb : v.b ∈ maximalIdeal A
  · exact nodePointLabel_add_first_middle D v w hk hkw hm hb
  have hbu : IsUnit v.b := not_not.mp hb
  obtain ⟨v', hv', hvl⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  rw [hv'] at hvl
  have hvb : v'.b ∈ maximalIdeal A := by
    rcases (nodeBranchLabel_opposite_iff hk (by omega) v.b v'.b).mp hvl with h | h
    · exact (h.1 hbu).elim
    · exact h.2
  have hs := nodePointLabel_add_first_middle D v' w' (by omega) (by omega) (by omega) hvb
  rw [← neg_add, nodePointLabel_neg, nodePointLabel_neg, nodePointLabel_neg, ← neg_add] at hs
  exact neg_injective hs

end FLT.Mazur
