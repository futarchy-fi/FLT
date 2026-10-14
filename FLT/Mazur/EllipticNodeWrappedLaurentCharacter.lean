/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTripleLaurentCharacter
public import FLT.Mazur.EllipticNodeInverseResidues
public import FLT.Mazur.EllipticNodeLabelSeparation

/-!
# Original Laurent parameters across a branch change

If two first-branch points add to the second strict branch, the three primitive
depths sum to the model depth. The original tangent parameters have product
fixed by the leading a₆ coefficient. This is the wraparound case, including tangents.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}
include D

/-- Ordered first-branch inputs retain their characters when their sum changes branch. -/
theorem node_wrapped_sum_character_le
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hvw : v.depth ≤ w.depth) (hw : 2 * w.depth < n)
    (hu0 : 0 < u.depth) (hu : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) (hf : IsUnit u.b)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    v.depth + w.depth + u.depth = n ∧
      residue A (v.b + W.a₁ * v.a) * residue A (w.b + W.a₁ * w.a) * residue A u.b =
        residue A W.a₁ ^ 3 * residue A c₆ := by
  obtain ⟨u', hu', hul⟩ := exists_nodePointCoordinates_inverse D u (by omega)
  rw [hu'] at hul
  have hub : u'.b ∈ maximalIdeal A := by
    rcases (nodeBranchLabel_opposite_iff hu0 hu u.b u'.b).mp hul with h | h
    · exact (h.1 hf).elim
    · exact h.2
  have hs := node_depth_sum_of_first_triple D v w u' hv0 hvw hw (by omega) (by omega)
    hb hd hub
  have hc := node_first_triple_horizontal_character D v w u' hv0 hvw hw
    (by omega) (by omega) hb hd hub c₆ h6
  have hxa := (node_inverse_coordinate_residues D u u' (by omega)).2.1
  have hz := node_inverse_other_residue D u u' (by omega)
  rw [map_add, map_mul, (residue_eq_zero_iff _).mpr hub, zero_add, hxa] at hz
  rw [hxa] at hc
  refine ⟨by simpa only [hu'] using hs, ?_⟩
  simp only [map_add, map_mul, (residue_eq_zero_iff _).mpr hb,
    (residue_eq_zero_iff _).mpr hd, zero_add]
  linear_combination residue A W.a₁ ^ 2 * residue A v.a * residue A w.a * hz -
    residue A W.a₁ ^ 3 * hc

/-- The branch-changing character formula does not depend on the input order. -/
theorem node_wrapped_sum_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n)
    (hu0 : 0 < u.depth) (hu : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) (hf : IsUnit u.b)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    v.depth + w.depth + u.depth = n ∧
      residue A (v.b + W.a₁ * v.a) * residue A (w.b + W.a₁ * w.a) * residue A u.b =
        residue A W.a₁ ^ 3 * residue A c₆ := by
  rcases le_total v.depth w.depth with h | h
  · exact node_wrapped_sum_character_le D v w u hv0 h hw hu0 hu hb hd hf c₆ h6
  · let t : NodePointCoordinates A W π (Q + P) :=
      { u with represents := (add_comm Q P).trans u.represents }
    obtain ⟨hs, hc⟩ := node_wrapped_sum_character_le D w v t hw0 h hv hu0 hu hd hb hf c₆ h6
    exact ⟨by simpa only [t, add_comm] using hs, by simpa only [t, mul_comm] using hc⟩

end FLT.Mazur
