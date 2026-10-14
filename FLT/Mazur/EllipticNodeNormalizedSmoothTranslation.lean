/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeNormalizedMiddleAddition
public import FLT.Mazur.EllipticNodeLabelDecode

/-!
# Original smooth translation multiplies normalized nodal parameters

The proved label law supplies the output depth and branch. Opposite sums
then compute its parameter using the actual smooth character of the
translator, on both strict branches and at the midpoint.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P : (W.map (algebraMap A K)).toProjective.Point} (T : ellipticE0 A W)
  (v : NodePointCoordinates A W π P) (u : NodePointCoordinates A W π (P + T.val))

include D

/-- A smooth translator leaves the actual output's bounded branch label unchanged. -/
theorem node_smooth_translate_branchLabel :
    nodeBranchLabel n u.depth u.b = nodeBranchLabel n v.depth v.b := by
  rw [← nodePointLabel_eq_of_coordinates D u, ← nodePointLabel_eq_of_coordinates D v]
  exact nodePointLabel_add_smooth_right D P T.val T.property

variable [DecidableEq (ResidueField A)]

/-- The positive parameter is multiplied by the original smooth character. -/
theorem node_positive_parameter_smooth_translate
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (hu : u.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) :
    nodePositiveParameter u = nodePositiveParameter v *
      (Additive.toMul (splitDepthSmoothCharacter D T)).val := by
  have hl := node_smooth_translate_branchLabel D T v u
  rw [nodeBranchLabel_of_mem n v.depth hb] at hl
  obtain ⟨hd, hb'⟩ := nodeBranchLabel_decode_positive D.depth_pos hv0 (by omega) hu u.b hl
  have hub := hb'.resolve_left (by omega)
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  have hvb : IsUnit v'.b := by
    have ht := (node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
      n v.depth hv0 hv D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
      v.a v.b v.primitive v.equation).2
    have hvu : IsUnit (v.b + W.a₁ * v.a) := by
      rcases ht with h | h
      · exact h.2
      · exact (hb h.1).elim
    rw [← residue_ne_zero_iff_isUnit, (node_inverse_coordinate_residues D v v' (by omega)).2.2]
    exact neg_ne_zero.mpr ((residue_ne_zero_iff_isUnit _).mpr hvu)
  have hc := node_opposite_parameter_smooth D u v' (by omega) (by omega)
    (by omega) hub hvb
  have he : (⟨P + T.val + -P, u.smooth_add_of_opposite D v'
      (by omega) (by omega) (by omega) hub hvb⟩ : ellipticE0 A W) = T := by
    apply Subtype.ext
    dsimp
    abel
  rw [he, node_inverse_parameter D v v' (by omega)] at hc
  have hn : nodePositiveParameter v ≠ 0 := by
    have hn' := nodeNegativeParameter_ne_zero D v' hvb
    rw [node_inverse_parameter D v v' (by omega)] at hn'
    intro hz
    exact hn' (by rw [hz, inv_zero])
  apply mul_left_cancel₀ (inv_ne_zero hn)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  simpa only [mul_comm] using hc

/-- The negative parameter is multiplied by the same original smooth character. -/
theorem node_negative_parameter_smooth_translate
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (hu : u.depth ≤ n / 2)
    (hb : IsUnit v.b) :
    nodeNegativeParameter u = nodeNegativeParameter v *
      (Additive.toMul (splitDepthSmoothCharacter D T)).val := by
  have hl := node_smooth_translate_branchLabel D T v u
  rw [nodeBranchLabel_eq_neg_of_unit n v.depth hb] at hl
  obtain ⟨hd, hub⟩ := nodeBranchLabel_decode_negative D.depth_pos hv0 hv hu u.b hl
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  have hvb := node_inverse_second_branch_mem D v v' hv0 hv hb
  have hc := node_opposite_parameter_smooth D v' u (by omega) (by omega)
    (by omega) hvb hub
  have he : (⟨-P + (P + T.val), v'.smooth_add_of_opposite D u
      (by omega) (by omega) (by omega) hvb hub⟩ : ellipticE0 A W) = T := by
    apply Subtype.ext
    dsimp
    abel
  rw [he, node_inverse_positive_parameter D v v' (by omega)] at hc
  have hn := nodeNegativeParameter_ne_zero D v hb
  apply mul_left_cancel₀ (inv_ne_zero hn)
  simpa only [← mul_assoc, inv_mul_cancel₀ hn, one_mul] using hc

/-- The positive midpoint parameter has the identical smooth translation rule. -/
theorem node_middle_parameter_smooth_translate
    (hv : 2 * v.depth = n) (hu : u.depth ≤ n / 2) :
    nodePositiveParameter u = nodePositiveParameter v *
      (Additive.toMul (splitDepthSmoothCharacter D T)).val := by
  have hd := nodeBranchLabel_eq_imp_depth D.depth_pos hu (by omega) u.b v.b
    (node_smooth_translate_branchLabel D T v u)
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  have hc := node_middle_smooth_character D v' u (by omega) (by omega)
  have he : (⟨-P + (P + T.val), v'.smooth_add_of_middle D u
      (by omega) (by omega)⟩ : ellipticE0 A W) = T := by
    apply Subtype.ext
    dsimp
    abel
  rw [he, (node_inverse_coordinate_residues D v v' (by omega)).2.2] at hc
  have hx : residue A (u.b + W.a₁ * u.a) = residue A (v.b + W.a₁ * v.a) *
      (Additive.toMul (splitDepthSmoothCharacter D T)).val := by linear_combination hc
  dsimp [nodePositiveParameter]
  rw [hx]
  ring

end FLT.Mazur
