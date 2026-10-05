/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSameBranchLabels
public import FLT.Mazur.EllipticNodeComponentBound

/-!
# Full additivity of the nodal point label

Negation reflects the first-branch calculation to the second branch. Smooth
inputs, opposite branches and midpoint inputs have already been settled.
The resulting addition law has no reduction or classification hypothesis
beyond the explicit deep split-node coefficients.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Two second-branch points satisfy label addition, including doubling. -/
theorem nodePointLabel_add_second_second
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 0 < v.depth) (hw : 0 < w.depth) (hvn : 2 * v.depth < n) (hwn : 2 * w.depth < n)
    (hb : IsUnit v.b) (hd : IsUnit w.b) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  obtain ⟨v', hv', hvl⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', hwl⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  rw [hv'] at hvl
  rw [hw'] at hwl
  have hvb : v'.b ∈ maximalIdeal A := by
    rcases (nodeBranchLabel_opposite_iff hv hvn v.b v'.b).mp hvl with h | h
    · exact (h.1 hb).elim
    · exact h.2
  have hwb : w'.b ∈ maximalIdeal A := by
    rcases (nodeBranchLabel_opposite_iff hw hwn w.b w'.b).mp hwl with h | h
    · exact (h.1 hd).elim
    · exact h.2
  have hs := nodePointLabel_add_first_first D v' w' (by omega) (by omega)
    (by omega) (by omega) hvb hwb
  rw [← neg_add, nodePointLabel_neg, nodePointLabel_neg, nodePointLabel_neg, ← neg_add] at hs
  exact neg_injective hs

/-- The canonical nodal label is additive on the actual generic elliptic-curve group. -/
theorem nodePointLabel_add (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  by_cases hp : SmoothReduction A W P
  · exact nodePointLabel_add_of_smooth D P Q (Or.inl hp)
  by_cases hq : SmoothReduction A W Q
  · exact nodePointLabel_add_of_smooth D P Q (Or.inr hq)
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  have hv0 := v.depth_pos_of_not_smooth D hp
  have hw0 := w.depth_pos_of_not_smooth D hq
  by_cases hvm : 2 * v.depth = n
  · by_cases hwm : 2 * w.depth = n
    · exact nodePointLabel_add_of_middle D v w hvm hwm
    · simpa only [add_comm] using nodePointLabel_add_shallower_middle D w v hw0 (by omega) hvm
  by_cases hwm : 2 * w.depth = n
  · exact nodePointLabel_add_shallower_middle D v w hv0 (by omega) hwm
  by_cases hvb : v.b ∈ maximalIdeal A
  · by_cases hwb : w.b ∈ maximalIdeal A
    · exact nodePointLabel_add_first_first D v w hv0 hw0 (by omega) (by omega) hvb hwb
    · exact nodePointLabel_add_first_unit D v w hv0 hw0 hv hw hvb (not_not.mp hwb)
  · by_cases hwb : w.b ∈ maximalIdeal A
    · exact nodePointLabel_add_of_distinct_branches D v w hv0 hw0 hv hw
        (Or.inr ⟨not_not.mp hvb, hwb⟩)
    · exact nodePointLabel_add_second_second D v w hv0 hw0 (by omega) (by omega)
        (not_not.mp hvb) (not_not.mp hwb)

end FLT.Mazur
