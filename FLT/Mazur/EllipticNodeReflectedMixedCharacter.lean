/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeMixedLaurentCharacter
public import FLT.Mazur.EllipticNodeInverseResidues

/-!
# Reflected mixed-branch arithmetic characters

A shallower second-branch point plus a deeper point with unit opposite tangent
character has first-branch output at the depth difference. Inverting the actual
points transports the original Laurent coordinates, including middle inputs.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- The inverse of a strict second-branch witness has vanishing vertical residue. -/
theorem node_inverse_second_branch_mem
    (v : NodePointCoordinates A W π P) (v' : NodePointCoordinates A W π (-P))
    (hk : 0 < v.depth) (hn : 2 * v.depth < n) (hb : IsUnit v.b) :
    v'.b ∈ maximalIdeal A := by
  obtain ⟨_, ht⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero
    D.maximalIdeal_eq n v.depth hk hn D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation
  have hz : v.b + W.a₁ * v.a ∈ maximalIdeal A := by
    rcases ht with h | h
    · exact (h.1 hb).elim
    · exact h.2
  rw [← residue_eq_zero_iff, (node_inverse_coordinate_residues D v v' (by omega)).2.2,
    (residue_eq_zero_iff _).mpr hz, neg_zero]

/-- Reflected mixed sums have an actual primitive witness at the depth difference. -/
theorem exists_nodePointCoordinates_add_of_unit_tangent
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : IsUnit v.b) (hd : IsUnit (w.b + W.a₁ * w.a)) :
    ∃ u : NodePointCoordinates A W π (P + Q), u.depth = w.depth - v.depth := by
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w hw
  have hvb := node_inverse_second_branch_mem D v v' hk (by omega) hb
  have hwb : IsUnit w'.b := by
    rw [← residue_ne_zero_iff_isUnit,
      (node_inverse_coordinate_residues D w w' hw).2.2]
    exact neg_ne_zero.mpr ((residue_ne_zero_iff_isUnit _).mpr hd)
  obtain ⟨s, hs, _, _⟩ := exists_nodePointCoordinates_add_of_first_unit D v' w'
    (by omega) (by omega) (by omega) hvb hwb
  obtain ⟨u, hu, _⟩ := exists_nodePointCoordinates_inverse D s (by omega)
  have he : P + Q = -(-P + -Q) := by simp only [← neg_add, neg_neg]
  exact ⟨{ u with represents := he.trans u.represents }, by dsimp; omega⟩

/-- Original first-branch residues of the reflected sum, without a chosen inverse witness. -/
theorem node_add_unit_tangent_residues
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : IsUnit v.b) (hd : IsUnit (w.b + W.a₁ * w.a)) :
    u.depth = w.depth - v.depth ∧
      residue A v.a * residue A u.a = residue A W.a₁ * residue A (w.b + W.a₁ * w.a) ∧
      residue A u.b = 0 := by
  obtain ⟨t, ht⟩ := exists_nodePointCoordinates_add_of_unit_tangent D v w hk hkw hw hb hd
  have hu := (u.unique D.uniformizer_ne_zero D.maximalIdeal_eq t).1.trans ht
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w hw
  obtain ⟨u', _, _⟩ := exists_nodePointCoordinates_inverse D u (by omega)
  have hvb := node_inverse_second_branch_mem D v v' hk (by omega) hb
  have hwr := node_inverse_coordinate_residues D w w' hw
  have hwb : IsUnit w'.b := by
    rw [← residue_ne_zero_iff_isUnit, hwr.2.2]
    exact neg_ne_zero.mpr ((residue_ne_zero_iff_isUnit _).mpr hd)
  let s : NodePointCoordinates A W π (-P + -Q) :=
    { u' with represents := (neg_add P Q).symm.trans u'.represents }
  obtain ⟨_, hx, hy⟩ := node_add_first_unit_residues D v' w' s
    (by omega) (by omega) (by omega) hvb hwb
  have hvr := node_inverse_coordinate_residues D v v' (by omega)
  have hur := node_inverse_coordinate_residues D u u' (by omega)
  change residue A v'.a * residue A u'.a = _ at hx
  change residue A u'.b = -residue A W.a₁ * residue A u'.a at hy
  rw [hvr.2.1, hur.2.1, hwr.2.2, neg_mul_neg] at hx
  rw [hur.2.2, hur.2.1, map_add, map_mul] at hy
  exact ⟨hu, hx, by linear_combination -hy⟩

/-- The reflected original characters obey the quotient law with the inversion sign. -/
theorem node_add_unit_tangent_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : IsUnit v.b) (hd : IsUnit (w.b + W.a₁ * w.a)) :
    residue A v.b * residue A (u.b + W.a₁ * u.a) =
      -(residue A W.a₁ ^ 3 * residue A (w.b + W.a₁ * w.a)) := by
  obtain ⟨_, hx, hy⟩ := node_add_unit_tangent_residues D v w u hk hkw hw hb hd
  obtain ⟨v', _, _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  have hz := node_inverse_second_branch_mem D v v' hk (by omega) hb
  have hv := (node_inverse_coordinate_residues D v v' (by omega)).2.2
  rw [(residue_eq_zero_iff _).mpr hz, map_add, map_mul] at hv
  rw [map_add, map_mul, hy, zero_add]
  linear_combination residue A W.a₁ * residue A u.a * hv - residue A W.a₁ ^ 2 * hx

end FLT.Mazur
