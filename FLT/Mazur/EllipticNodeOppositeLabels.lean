/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentInverse
public import FLT.Mazur.EllipticNodeOppositeAddition

/-!
# Label addition for equal-depth opposite branches

Coordinate witnesses on the two strict branches sum into E₀, and their
labels cancel in Z/nZ. The assertions concern the actual generic points.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D
/-- Equal positive depths on opposite strict branches give a smooth actual sum. -/
theorem NodePointCoordinates.smooth_add_of_opposite
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) : SmoothReduction A W (P + Q) := by
  classical
  obtain ⟨ha, _⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero
    D.maximalIdeal_eq n v.depth hk hkn D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation
  obtain ⟨_, ht⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero
    D.maximalIdeal_eq n w.depth (by omega) (by omega)
    D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem w.a w.b w.primitive w.equation
  have hdt : w.b + W.a₁ * w.a ∈ maximalIdeal A := by
    rcases ht with h | h
    · exact (h.1 hd).elim
    · exact h.2
  have hπm : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hs := smoothReduction_add_of_node_opposite A W D.uniformizer_ne_zero hπm
    v.depth hk v.a v.b w.a w.b v.nonsingular (by simpa only [he] using w.nonsingular)
    D.a₁_unit D.a₂_mem (Ideal.pow_le_self (by omega) D.a₃_mem)
    (Ideal.pow_le_self (by omega) D.a₄_mem)
    (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem) ha hb hd hdt
  rw [toProjective_add] at hs
  rw [v.represents, w.represents]
  simpa only [he] using hs

/-- The label addition law for equal positive depths on opposite strict branches. -/
theorem nodePointLabel_add_of_opposite
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  rw [(nodePointLabel_eq_zero_iff D (P + Q)).mpr (v.smooth_add_of_opposite D w hk hkn he hb hd),
    nodePointLabel_eq_of_coordinates D v, nodePointLabel_eq_of_coordinates D w,
    nodeBranchLabel_of_mem n v.depth hb, nodeBranchLabel_of_unit (by omega) hd, he,
    add_neg_cancel]

/-- Opposite equal-depth branches represent opposite classes in the actual quotient. -/
theorem NodePointCoordinates.component_eq_neg_of_opposite
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    ellipticComponentHom A W P = -ellipticComponentHom A W Q := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← map_add, ellipticComponentHom_eq_zero]
  exact v.smooth_add_of_opposite D w hk hkn he hb hd

end FLT.Mazur
