/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeFirstSumLaurentCharacter

/-!
# Original Laurent characters when a sum reaches the midpoint

At the even middle depth both tangent factors are units and their product is
the normalized a₆ residue. Subtracting a first-branch input computes the other
factor of the sum, and hence its original vertical Laurent parameter.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}
include D

/-- The middle point's two original tangent residues multiply to normalized a₆. -/
theorem node_middle_tangent_character
    (v : NodePointCoordinates A W π P) (hm : 2 * v.depth = n)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    residue A v.b * residue A (v.b + W.a₁ * v.a) = residue A c₆ := by
  obtain ⟨b3, hb3, h3⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  obtain ⟨b4, hb4, h4⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
  have h := node_scaled_tangent_equation W D.uniformizer_ne_zero
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
    (by have := D.depth_pos; omega) v.a v.b b3 b4 c₆ D.a₂_mem hb3 hb4 h3 h4
    (by simpa only [hm] using h6) v.equation
  simpa only [map_add, map_mul] using h

/-- First-branch inputs reaching the middle have depths adding to that middle depth. -/
theorem node_first_middle_sum_depth
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hm : 2 * u.depth = n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    u.depth = v.depth + w.depth := by
  have he := nodePointLabel_add D P Q
  rw [nodePointLabel_eq_of_coordinates D u, nodePointLabel_eq_of_coordinates D v,
    nodePointLabel_eq_of_coordinates D w, (nodeBranchLabel_middle hm u.b).1,
    nodeBranchLabel_of_mem n _ hb, nodeBranchLabel_of_mem n _ hd, ← Nat.cast_add] at he
  have h := (ZMod.natCast_eq_natCast_iff' u.depth (v.depth + w.depth) n).mp he
  have hn := D.depth_pos
  simpa only [Nat.mod_eq_of_lt (by omega : u.depth < n),
    Nat.mod_eq_of_lt (by omega : v.depth + w.depth < n)] using h

/-- The original middle Laurent parameter is determined by both first-branch inputs. -/
theorem node_first_middle_sum_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hm : 2 * u.depth = n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    residue A (v.b + W.a₁ * v.a) * residue A (w.b + W.a₁ * w.a) * residue A u.b =
      residue A W.a₁ ^ 3 * residue A c₆ := by
  have hdepth := node_first_middle_sum_depth D v w u hv hw hm hb hd
  obtain ⟨u', hu', _⟩ := exists_nodePointCoordinates_inverse D u (by omega)
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  have hva := (node_inverse_coordinate_residues D v v' (by omega)).2.1
  have hub := (node_inverse_coordinate_residues D u u' (by omega)).2.2
  have hunit : IsUnit u'.b := (u'.units_of_middle D (by omega)).1
  have hc : Q + -(P + Q) = -P := by abel
  let t : NodePointCoordinates A W π (Q + -(P + Q)) :=
    { v' with represents := hc.trans v'.represents }
  have hr := (node_add_first_unit_residues D w u' t hw0 (by omega) (by omega) hd hunit).2.1
  change residue A w.a * residue A v'.a = -residue A W.a₁ * residue A u'.b at hr
  rw [hva, hub] at hr
  have ht := node_middle_tangent_character D u hm c₆ h6
  simp only [map_add, map_mul, (residue_eq_zero_iff _).mpr hb,
    (residue_eq_zero_iff _).mpr hd, zero_add]
  linear_combination residue A W.a₁ ^ 2 * residue A u.b * hr + residue A W.a₁ ^ 3 * ht

end FLT.Mazur
