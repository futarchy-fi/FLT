/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSameBranchSlope
public import FLT.Mazur.EllipticNodeComponentInverse
public import FLT.Mazur.EllipticNodeLabelSeparation

/-!
# Equal-depth addition on the first strict branch

The unit second denominator gives an integral slope, whose residue is zero.
The actual addition formulas put the sum over the node. In particular, such
points cannot represent opposite component classes.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Points of the same strict depth on the first branch cannot sum into E₀. -/
theorem NodePointCoordinates.not_smooth_add_of_first_branch
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    ¬ SmoothReduction A W (P + Q) := by
  classical
  obtain ⟨hc, _⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
    n w.depth (by omega) (by omega) D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    w.a w.b w.primitive w.equation
  obtain ⟨e₃, he₃, h3e⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  obtain ⟨e₄, he₄, h4e⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
  have hu := node_same_branch_denominator_unit W D.a₁_unit hc hb hd he₃
  obtain ⟨l, hl, hy⟩ := exists_node_second_slope A W D.uniformizer_ne_zero v.depth
    v.a v.b w.a w.b e₃ e₄ h3e h4e hu v.nonsingular.1
    (by simpa only [he] using w.nonsingular.1)
  have hπm : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hr := node_equal_depth_second_residue A W D.uniformizer_ne_zero hπm v.depth hk
    v.a v.b w.a w.b l e₃ e₄ D.a₂_mem he₃ he₄ h3e h4e v.nonsingular.1
    (by simpa only [he] using w.nonsingular.1) (fun h => hy h.2) hl
  have hl0 : residue A l = 0 := by
    have hb0 := (residue_eq_zero_iff _).mpr hb
    have hd0 := (residue_eq_zero_iff _).mpr hd
    simp only [hb0, hd0, zero_add, mul_zero, neg_zero] at hr
    exact (mul_eq_zero.mp hr).resolve_left
      (mul_ne_zero ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit)
        ((residue_ne_zero_iff_isUnit _).mpr hc))
  have hm (e : A) : π ^ v.depth * e ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_right e
      (Ideal.pow_le_self (Nat.ne_of_gt hk) (Ideal.pow_mem_pow hπm v.depth))
  have hs := not_smoothReduction_add_of_node_slope A W _ _ _ _ l v.nonsingular
    (by simpa only [he] using w.nonsingular) (fun h => hy h.2) hl D.a₂_mem
    (Ideal.pow_le_self (by omega) D.a₃_mem) (Ideal.pow_le_self (by omega) D.a₄_mem)
    (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem)
    (hm v.a) (hm v.b) (hm w.a) (Or.inl hl0)
  rw [toProjective_add] at hs
  rw [v.represents, w.represents]
  simpa only [he] using hs

/-- Points of the same strict depth and tangent branch cannot sum into E₀. -/
theorem NodePointCoordinates.not_smooth_add_of_same_branch
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A ↔ w.b ∈ maximalIdeal A) :
    ¬ SmoothReduction A W (P + Q) := by
  by_cases hv : v.b ∈ maximalIdeal A
  · exact v.not_smooth_add_of_first_branch D w hk hkn he hv (hb.mp hv)
  have hw : w.b ∉ maximalIdeal A := fun h => hv (hb.mpr h)
  obtain ⟨v', hv', hvl⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', hwl⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  rw [hv'] at hvl
  rw [hw'] at hwl
  have hvm : v'.b ∈ maximalIdeal A := by
    rcases (nodeBranchLabel_opposite_iff hk hkn v.b v'.b).mp hvl with h | h
    · exact (hv h.1).elim
    · exact h.2
  have hwm : w'.b ∈ maximalIdeal A := by
    rcases (nodeBranchLabel_opposite_iff (by omega) (by omega) w.b w'.b).mp hwl with h | h
    · exact (hw h.1).elim
    · exact h.2
  have hs := v'.not_smooth_add_of_first_branch D w' (by omega) (by omega) (by omega) hvm hwm
  intro h
  apply hs
  simpa only [neg_add] using h.neg A W

end FLT.Mazur
