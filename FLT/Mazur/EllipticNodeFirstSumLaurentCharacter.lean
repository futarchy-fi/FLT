/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeMixedLaurentCharacter
public import FLT.Mazur.EllipticNodeInverseResidues
public import FLT.Mazur.EllipticNodeLabelAdditivity

/-!
# Laurent multiplication when a first-branch sum stays on that branch

The additive labels first determine the exact output depth. Applying the
mixed-branch residue formula after subtracting a summand then computes the
original horizontal and tangent characters of the actual sum, including doubling.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}
include D

/-- A first-branch output has the sum of the two strict input depths. -/
theorem node_first_sum_depth
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A)
    (hf : u.b ∈ maximalIdeal A) : u.depth = v.depth + w.depth := by
  have he := nodePointLabel_add D P Q
  rw [nodePointLabel_eq_of_coordinates D u, nodePointLabel_eq_of_coordinates D v,
    nodePointLabel_eq_of_coordinates D w, nodeBranchLabel_of_mem n _ hf,
    nodeBranchLabel_of_mem n _ hb, nodeBranchLabel_of_mem n _ hd, ← Nat.cast_add] at he
  have hm := (ZMod.natCast_eq_natCast_iff' u.depth (v.depth + w.depth) n).mp he
  simpa only [Nat.mod_eq_of_lt (by omega : u.depth < n),
    Nat.mod_eq_of_lt (by omega : v.depth + w.depth < n)] using hm

/-- The actual horizontal leading coefficients multiply with the factor a₁ squared. -/
theorem node_first_sum_horizontal_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A)
    (hf : u.b ∈ maximalIdeal A) :
    residue A v.a * residue A w.a = residue A W.a₁ ^ 2 * residue A u.a := by
  have hdepth := node_first_sum_depth D v w u hv hw hu hb hd hf
  obtain ⟨u', hu', _⟩ := exists_nodePointCoordinates_inverse D u (by omega)
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨_, hva, _⟩ := node_inverse_coordinate_residues D v v' (by omega)
  obtain ⟨_, _, hub⟩ := node_inverse_coordinate_residues D u u' (by omega)
  have hunit : IsUnit u'.b := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have ha := (node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
      n u.depth (by omega) hu D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
      u.a u.b u.primitive u.equation).1
    rw [hub, map_add, map_mul, (residue_eq_zero_iff _).mpr hf, zero_add]
    exact neg_ne_zero.mpr ((D.a₁_unit.mul ha).map (residue A)).ne_zero
  have hc : Q + -(P + Q) = -P := by abel
  let t : NodePointCoordinates A W π (Q + -(P + Q)) :=
    { v' with represents := hc.trans v'.represents }
  have hr := (node_add_first_unit_residues D w u' t hw0 (by omega) (by omega) hd hunit).2.1
  change residue A w.a * residue A v'.a = -residue A W.a₁ * residue A u'.b at hr
  rw [hva, hub, map_add, map_mul, (residue_eq_zero_iff _).mpr hf, zero_add] at hr
  linear_combination hr

/-- The original positive Laurent parameters multiply with the factor a₁ cubed. -/
theorem node_first_sum_laurent_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A)
    (hf : u.b ∈ maximalIdeal A) :
    residue A (v.b + W.a₁ * v.a) * residue A (w.b + W.a₁ * w.a) =
      residue A W.a₁ ^ 3 * residue A (u.b + W.a₁ * u.a) := by
  have h := node_first_sum_horizontal_character D v w u hv0 hw0 hv hw hu hb hd hf
  simp only [map_add, map_mul, (residue_eq_zero_iff _).mpr hb,
    (residue_eq_zero_iff _).mpr hd, (residue_eq_zero_iff _).mpr hf, zero_add]
  linear_combination residue A W.a₁ ^ 2 * h

end FLT.Mazur
