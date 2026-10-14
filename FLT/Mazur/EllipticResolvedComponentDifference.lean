/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedMiddleTranslationEquality
public import FLT.Mazur.EllipticNodeReflectedMixedCharacter

/-!
# Arithmetic differences detect equality on each resolved component

On each fixed strict component, the midpoint component and E₀, equality of
actual resolved specializations is equivalent to the difference entering E₁.
The strict cases include the final odd-depth chart. No group structure on the
resolved fiber is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- On a strict positive component, equality is exactly the E₁ difference relation. -/
theorem resolvedSplitSmoothPoint_positive_eq_iff_difference
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hn : 2 * v.depth < n) (he : w.depth = v.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      InfinityReduction A W (P - Q) := by
  obtain ⟨w', hw', hul⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  rw [hw'] at hul
  have hwb : IsUnit w'.b := by
    rcases (nodeBranchLabel_opposite_iff (by omega) (by omega) w.b w'.b).mp hul with h | h
    · exact h.2
    · exact (hd h.1).elim
  rw [resolvedSplitSmoothPoint_strict_positive_eq_iff A D v.depth hk hn P Q v rfl w he hb hd,
    sub_eq_add_neg, node_opposite_sum_infinity_iff D v w' hk hn (by omega) hb hwb,
    (node_inverse_coordinate_residues D w w' (by omega)).2.2, neg_inj, eq_comm]

/-- On a strict negative component, equality is exactly the E₁ difference relation. -/
theorem resolvedSplitSmoothPoint_negative_eq_iff_difference
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hn : 2 * v.depth < n) (he : w.depth = v.depth)
    (hb : IsUnit v.b) (hd : IsUnit w.b) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      InfinityReduction A W (P - Q) := by
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  have hwb := node_inverse_second_branch_mem D w w' (by omega) (by omega) hd
  rw [resolvedSplitSmoothPoint_strict_negative_eq_iff A D v.depth hk hn P Q v rfl w he hb hd,
    sub_eq_add_neg, add_comm P (-Q),
    node_opposite_sum_infinity_iff D w' v (by omega) (by omega) (by omega) hwb hb,
    node_inverse_other_residue D w w' (by omega), neg_neg]

/-- On the even midpoint component, equality is exactly the E₁ difference relation. -/
theorem resolvedSplitSmoothPoint_middle_eq_iff_difference
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      InfinityReduction A W (P - Q) := by
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  rw [resolvedSplitSmoothPoint_middle_character_eq_iff A D P Q v w hv hw, sub_eq_add_neg,
    node_middle_sum_infinity_iff D v w' hv (by omega),
    node_inverse_other_residue D w w' (by omega), neg_neg]

/-- On E₀, equality is exactly the kernel relation of the actual smooth-reduction homomorphism. -/
theorem resolvedSplitSmoothPoint_e0_eq_iff_difference (P Q : ellipticE0 A W) :
    resolvedSplitSmoothPoint A D P.val = resolvedSplitSmoothPoint A D Q.val ↔
      InfinityReduction A W (P.val - Q.val) := by
  classical
  rw [resolvedSplitSmoothPoint_e0_character_eq_iff, splitDepthSmoothCharacter_eq_iff,
    ← sub_eq_zero, ← map_sub]
  exact smoothReductionPoint_eq_zero_iff A W (P - Q)

end FLT.Mazur.WeierstrassDividedDepth
