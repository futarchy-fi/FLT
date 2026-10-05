/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSameBranchAddition
public import FLT.Mazur.EllipticNodeLabelFibers
public import FLT.Mazur.EllipticNodeUnequalDepthAddition

/-!
# Component classes determine nodal labels

Unequal depths separate classes. At a strict equal depth, the same-branch sum
obstruction detects the tangent branch after negation. Together with the
midpoint rule and E₀ this proves exact equality of the two equivalence relations.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Equal component classes at a strict positive depth have the same branch label. -/
theorem NodePointCoordinates.label_eq_of_strict_component
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hc : ellipticComponentHom A W P = ellipticComponentHom A W Q) :
    nodeBranchLabel n v.depth v.b = nodeBranchLabel n w.depth w.b := by
  obtain ⟨w', hw', hwl⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  have hs : SmoothReduction A W (P + -Q) := by
    simpa only [sub_eq_add_neg] using (ellipticComponentHom_eq_iff A W P Q).mp hc
  have ht : ¬ (v.b ∈ maximalIdeal A ↔ w'.b ∈ maximalIdeal A) :=
    fun h => v.not_smooth_add_of_same_branch D w' hk hkn (by omega) h hs
  have hopp : (v.b ∈ maximalIdeal A ∧ IsUnit w'.b) ∨
      (IsUnit v.b ∧ w'.b ∈ maximalIdeal A) := by
    by_cases hb : v.b ∈ maximalIdeal A
    · exact Or.inl ⟨hb, not_not.mp (fun hw => ht ⟨fun _ => hw, fun _ => hb⟩)⟩
    · have hw : w'.b ∈ maximalIdeal A := by
        by_contra hn
        exact ht ⟨fun h => (hb h).elim, fun h => (hn h).elim⟩
      exact Or.inr ⟨not_not.mp hb, hw⟩
  have hneg := (nodeBranchLabel_opposite_iff hk hkn v.b w'.b).mpr hopp
  have hd : w'.depth = v.depth := by omega
  rw [hd] at hwl
  exact (neg_injective (hwl.symm.trans hneg)).symm

/-- The actual component quotient and the nodal label have precisely the same fibers. -/
theorem ellipticComponentHom_eq_iff_nodePointLabel_eq :
    ellipticComponentHom A W P = ellipticComponentHom A W Q ↔
      nodePointLabel D P = nodePointLabel D Q := by
  refine ⟨?_, ellipticComponentHom_eq_of_nodePointLabel_eq D⟩
  intro hc
  by_cases hp : SmoothReduction A W P
  · have hq := (ellipticComponentHom_eq_zero A W Q).mp
      (hc.symm.trans ((ellipticComponentHom_eq_zero A W P).mpr hp))
    rw [(nodePointLabel_eq_zero_iff D P).mpr hp, (nodePointLabel_eq_zero_iff D Q).mpr hq]
  have hq : ¬ SmoothReduction A W Q := by
    intro hq
    exact hp ((ellipticComponentHom_eq_zero A W P).mp
      (hc.trans ((ellipticComponentHom_eq_zero A W Q).mpr hq)))
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  have hpos {T : (W.map (algebraMap A K)).toProjective.Point}
      (u : NodePointCoordinates A W π T) (ht : ¬ SmoothReduction A W T) : 0 < u.depth := by
    by_contra hn
    apply ht
    apply (nodePointLabel_eq_zero_iff D T).mp
    rw [nodePointLabel_eq_of_coordinates D u, show u.depth = 0 by omega, nodeBranchLabel_zero]
  have hv0 := hpos v hp
  have hw0 := hpos w hq
  have he : v.depth = w.depth := by
    rcases lt_trichotomy v.depth w.depth with h | h | h
    · exact (v.component_ne D w hv0 h hw hc).elim
    · exact h
    · exact (w.component_ne D v hw0 h hv hc.symm).elim
  rw [nodePointLabel_eq_of_coordinates D v, nodePointLabel_eq_of_coordinates D w]
  by_cases hm : 2 * v.depth = n
  · rw [(nodeBranchLabel_middle hm v.b).1,
      (nodeBranchLabel_middle (by omega : 2 * w.depth = n) w.b).1, he]
  · exact v.label_eq_of_strict_component D w hv0 (by omega) he hc

end FLT.Mazur
