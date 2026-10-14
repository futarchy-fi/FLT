/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeReflectedMixedCharacter
public import FLT.Mazur.EllipticNodeFirstSumLaurentCharacter
public import FLT.Mazur.EllipticNodeWrappedLaurentCharacter
public import FLT.Mazur.EllipticNodeMiddleSumLaurentCharacter

/-!
# Arithmetic characters of sums on the second branch

Invert actual points to transport the first-branch character laws. The
original vertical characters retain the minus sign from inversion, including
branch changes and sums that reach the even middle component.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}
include D

/-- A second-branch sum that stays strict has the sum depth and signed product character. -/
theorem node_second_sum_laurent_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth) (hu0 : 0 < u.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : IsUnit v.b) (hd : IsUnit w.b) (hf : IsUnit u.b) :
    u.depth = v.depth + w.depth ∧
      residue A v.b * residue A w.b = -(residue A W.a₁ ^ 3 * residue A u.b) := by
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  obtain ⟨u', hu', _⟩ := exists_nodePointCoordinates_inverse D u (by omega)
  have hvb := node_inverse_second_branch_mem D v v' hv0 hv hb
  have hwb := node_inverse_second_branch_mem D w w' hw0 hw hd
  have hub := node_inverse_second_branch_mem D u u' hu0 hu hf
  let t : NodePointCoordinates A W π (-P + -Q) :=
    { u' with represents := (neg_add P Q).symm.trans u'.represents }
  have hs := node_first_sum_depth D v' w' t (by omega) (by omega) (by dsimp [t]; omega)
    hvb hwb hub
  have hc := node_first_sum_laurent_character D v' w' t (by omega) (by omega)
    (by omega) (by omega) (by dsimp [t]; omega) hvb hwb hub
  change residue A (v'.b + W.a₁ * v'.a) * residue A (w'.b + W.a₁ * w'.a) =
    residue A W.a₁ ^ 3 * residue A (u'.b + W.a₁ * u'.a) at hc
  rw [node_inverse_other_residue D v v' (by omega),
    node_inverse_other_residue D w w' (by omega),
    node_inverse_other_residue D u u' (by omega), neg_mul_neg, mul_neg] at hc
  exact ⟨by dsimp [t] at hs; omega, hc⟩

/-- A second-branch sum changing to the first branch has the signed wraparound coefficient. -/
theorem node_second_wrapped_sum_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth) (hu0 : 0 < u.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : IsUnit v.b) (hd : IsUnit w.b) (hf : u.b ∈ maximalIdeal A)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    v.depth + w.depth + u.depth = n ∧
      residue A v.b * residue A w.b * residue A (u.b + W.a₁ * u.a) =
        -(residue A W.a₁ ^ 3 * residue A c₆) := by
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  obtain ⟨u', hu', hul⟩ := exists_nodePointCoordinates_inverse D u (by omega)
  have hvb := node_inverse_second_branch_mem D v v' hv0 hv hb
  have hwb := node_inverse_second_branch_mem D w w' hw0 hw hd
  rw [hu'] at hul
  have hub : IsUnit u'.b := by
    rcases (nodeBranchLabel_opposite_iff hu0 hu u.b u'.b).mp hul with h | h
    · exact h.2
    · exact (hf h.1).elim
  let t : NodePointCoordinates A W π (-P + -Q) :=
    { u' with represents := (neg_add P Q).symm.trans u'.represents }
  obtain ⟨hs, hc⟩ := node_wrapped_sum_character D v' w' t (by omega) (by omega)
    (by omega) (by omega) (by dsimp [t]; omega) (by dsimp [t]; omega)
    hvb hwb hub c₆ h6
  change residue A (v'.b + W.a₁ * v'.a) * residue A (w'.b + W.a₁ * w'.a) *
    residue A u'.b = _ at hc
  rw [node_inverse_other_residue D v v' (by omega),
    node_inverse_other_residue D w w' (by omega),
    (node_inverse_coordinate_residues D u u' (by omega)).2.2] at hc
  exact ⟨by dsimp [t] at hs; omega, by linear_combination -hc⟩

/-- Second-branch inputs reaching the midpoint satisfy the same signed multiplication law. -/
theorem node_second_middle_sum_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hm : 2 * u.depth = n)
    (hb : IsUnit v.b) (hd : IsUnit w.b)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    u.depth = v.depth + w.depth ∧
      residue A v.b * residue A w.b = -(residue A W.a₁ ^ 3 * residue A u.b) := by
  obtain ⟨v', hv', _⟩ := exists_nodePointCoordinates_inverse D v (by omega)
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w (by omega)
  obtain ⟨u', hu', _⟩ := exists_nodePointCoordinates_inverse D u (by omega)
  have hvb := node_inverse_second_branch_mem D v v' hv0 hv hb
  have hwb := node_inverse_second_branch_mem D w w' hw0 hw hd
  let t : NodePointCoordinates A W π (-P + -Q) :=
    { u' with represents := (neg_add P Q).symm.trans u'.represents }
  have hs := node_first_middle_sum_depth D v' w' t (by omega) (by omega)
    (by dsimp [t]; omega) hvb hwb
  have hc := node_first_middle_sum_character D v' w' t (by omega) (by omega)
    (by omega) (by omega) (by dsimp [t]; omega) hvb hwb c₆ h6
  change residue A (v'.b + W.a₁ * v'.a) * residue A (w'.b + W.a₁ * w'.a) *
    residue A u'.b = _ at hc
  rw [node_inverse_other_residue D v v' (by omega),
    node_inverse_other_residue D w w' (by omega),
    (node_inverse_coordinate_residues D u u' (by omega)).2.2] at hc
  have ht := node_middle_tangent_character D u hm c₆ h6
  refine ⟨by dsimp [t] at hs; omega, ?_⟩
  apply mul_right_cancel₀ ((residue_ne_zero_iff_isUnit _).mpr (u.units_of_middle D hm).2)
  linear_combination -hc + residue A W.a₁ ^ 3 * ht

end FLT.Mazur
