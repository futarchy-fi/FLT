/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelSeparation
public import FLT.Mazur.EllipticNodeOppositeLabels
public import FLT.Mazur.EllipticNodeMiddleLabels

/-!
# Equal labels give equal actual component classes

At strict positive depth, negate one witness and use opposite-branch addition.
At the midpoint use the middle-depth addition theorem, and at zero use E₀.
This proves one direction of fiber equality; constancy on component classes
and full additivity remain separate obligations.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Equal strict branch labels identify actual component classes. -/
theorem NodePointCoordinates.component_eq_of_strict_label
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hl : nodeBranchLabel n v.depth v.b = nodeBranchLabel n w.depth w.b) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q := by
  obtain ⟨w', hw', hwlabel⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  have hneg : nodeBranchLabel n v.depth w'.b = -nodeBranchLabel n v.depth v.b := by
    rw [← he] at hw'
    rw [hw'] at hwlabel
    exact hwlabel.trans (congrArg Neg.neg hl.symm)
  rcases (nodeBranchLabel_opposite_iff hk hkn v.b w'.b).mp hneg with h | h
  · have hs := v.smooth_add_of_opposite D w' hk hkn (by omega) h.1 h.2
    exact (ellipticComponentHom_eq_iff A W P Q).mpr (by simpa only [sub_eq_add_neg] using hs)
  · have hs := w'.smooth_add_of_opposite D v (by omega) (by omega) (by omega) h.2 h.1
    exact (ellipticComponentHom_eq_iff A W P Q).mpr
      (by simpa only [sub_eq_add_neg, add_comm] using hs)

/-- Equality of labels implies equality in the actual quotient E/E₀. -/
theorem ellipticComponentHom_eq_of_nodePointLabel_eq
    (hl : nodePointLabel D P = nodePointLabel D Q) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q := by
  by_cases hp : SmoothReduction A W P
  · have hq := (nodePointLabel_eq_zero_iff D Q).mp
      (hl.symm.trans ((nodePointLabel_eq_zero_iff D P).mpr hp))
    rw [(ellipticComponentHom_eq_zero A W P).mpr hp, (ellipticComponentHom_eq_zero A W Q).mpr hq]
  have hq : ¬ SmoothReduction A W Q := by
    intro hq
    exact hp ((nodePointLabel_eq_zero_iff D P).mp
      (hl.trans ((nodePointLabel_eq_zero_iff D Q).mpr hq)))
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  rw [nodePointLabel_eq_of_coordinates D v, nodePointLabel_eq_of_coordinates D w] at hl
  have he := nodeBranchLabel_eq_imp_depth D.depth_pos hv hw v.b w.b hl
  by_cases hmid : 2 * v.depth = n
  · exact v.component_eq_of_middle D w hmid (by omega)
  have hk : 0 < v.depth := by
    by_contra hn
    have hz : v.depth = 0 := by omega
    apply hp
    apply (nodePointLabel_eq_zero_iff D P).mp
    rw [nodePointLabel_eq_of_coordinates D v, hz, nodeBranchLabel_zero]
  exact v.component_eq_of_strict_label D w hk (by omega) he hl

end FLT.Mazur
