/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDifferenceCoordinates
public import FLT.Mazur.EllipticNodeLabelSeparation

/-!
# Labels of unequal opposite-branch sums

The exact primitive difference coordinates compute the label of the actual
sum. A unit divided y-coordinate has the negative-depth label even at the
midpoint, where the two signs agree.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- A unit second coordinate has the negative-depth label, including the midpoint. -/
theorem nodeBranchLabel_eq_neg_of_unit {R : Type*} [CommRing R] [IsLocalRing R]
    (n k : ℕ) {b : R} (hb : IsUnit b) : nodeBranchLabel n k b = -(k : ZMod n) := by
  by_cases hm : 2 * k = n
  · exact (nodeBranchLabel_middle hm b).1.trans (nodeBranchLabel_middle hm b).2
  · exact nodeBranchLabel_of_unit hm hb

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Both tangent factors of a midpoint coordinate witness are units. -/
theorem NodePointCoordinates.units_of_middle (w : NodePointCoordinates A W π Q)
    (hm : 2 * w.depth = n) : IsUnit w.b ∧ IsUnit (w.b + W.a₁ * w.a) := by
  apply node_point_units_at_middle W D.uniformizer_ne_zero D.maximalIdeal_eq w.depth
    (by have := D.depth_pos; omega) D.a₂_mem
    (by simpa only [hm] using D.a₃_mem) (by simpa only [hm] using D.a₄_mem)
    (by simpa only [hm] using D.a₆_mem) (by simpa only [hm] using D.a₆_not_mem)
    w.a w.b w.equation

/-- The full label law for a shallower first-branch point and a deeper unit y-factor. -/
theorem nodePointLabel_add_of_first_unit
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  obtain ⟨u, hu, _, hub⟩ := exists_nodePointCoordinates_add_of_first_unit D v w hk hkw hw hb hd
  rw [nodePointLabel_eq_of_coordinates D u, nodePointLabel_eq_of_coordinates D v,
    nodePointLabel_eq_of_coordinates D w, nodeBranchLabel_eq_neg_of_unit n u.depth hub,
    nodeBranchLabel_of_mem n v.depth hb, nodeBranchLabel_eq_neg_of_unit n w.depth hd,
    hu, Nat.cast_sub (Nat.le_of_lt hkw)]
  ring

/-- A shallower first-branch point adds correctly to a midpoint point. -/
theorem nodePointLabel_add_first_middle
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hm : 2 * w.depth = n)
    (hb : v.b ∈ maximalIdeal A) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q :=
  nodePointLabel_add_of_first_unit D v w hk hkw (by omega) hb (w.units_of_middle D hm).1

end FLT.Mazur
