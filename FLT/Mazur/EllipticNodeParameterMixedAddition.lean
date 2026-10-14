/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterEvaluation
public import FLT.Mazur.EllipticNodeNormalizedMixedAddition
public import FLT.Mazur.EllipticNodeNormalizedMiddleAddition

/-!
# Global carry formulas for mixed branches and midpoints

The two unequal-depth orientations include a midpoint as the deeper input.
Opposite equal depths and two midpoints land on the original smooth locus.
All coefficients are those of the original Weierstrass equation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- A unit vertical tangent uses the negative parameter, including the midpoint. -/
theorem nodePointParameter_unit_branch (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (hv0 : 0 < v.depth)
    (hv : v.depth ≤ n / 2) (hb : IsUnit v.b) :
    nodePointParameter D c₆ P = nodeWrapParameter W c₆ * nodeNegativeParameter v := by
  by_cases hm : 2 * v.depth = n
  · exact nodePointParameter_middle_negative D c₆ h6 v hm
  · exact nodePointParameter_negative D c₆ v hv0 (by omega) hb

/-- A shallower positive input and a deeper unit tangent have no full-period carry. -/
theorem nodePointParameter_carry_positive_unit_lt (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv0 : 0 < v.depth) (hlt : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  have hc : nodePointCarry D P Q = 0 := by
    rw [nodePointCarry, nodePointLabel_val_positive D v (by omega) (Or.inr hb)]
    by_cases hm : 2 * w.depth = n
    · rw [nodePointLabel_val_positive D w hw (Or.inl hm)]
      exact ite_eq_right (by omega)
    · rw [nodePointLabel_val_negative D w (by omega) (by omega) hd]
      exact ite_eq_right (by omega)
  obtain ⟨u, hu, _, hub⟩ := exists_nodePointCoordinates_add_of_first_unit D v w hv0 hlt hw hb hd
  rw [hc, pow_zero, one_mul,
    nodePointParameter_positive D c₆ v hv0 (by omega) (Or.inr hb),
    nodePointParameter_unit_branch D c₆ h6 w (by omega) hw hd,
    nodePointParameter_negative D c₆ u (by omega) (by omega) hub,
    ← node_positive_negative_parameter_add D v w u hv0 hlt hw hb hd]
  ring

/-- A shallower negative input and a deeper positive tangent cross one full period. -/
theorem nodePointParameter_carry_negative_positive_lt
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv0 : 0 < v.depth) (hlt : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : IsUnit v.b) (hd : 2 * w.depth = n ∨ w.b ∈ maximalIdeal A) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  have hdt : IsUnit (w.b + W.a₁ * w.a) := by
    rcases hd with hm | hd
    · exact (w.units_of_middle D hm).2
    · have hm : 2 * w.depth ≠ n := fun h => hd (w.units_of_middle D h).1
      exact node_positive_tangent_isUnit D w (by omega) (by omega) hd
  have hc : nodePointCarry D P Q = 1 := by
    rw [nodePointCarry, nodePointLabel_val_negative D v hv0 (by omega) hb,
      nodePointLabel_val_positive D w hw hd]
    exact ite_eq_left (by omega)
  obtain ⟨u, hu⟩ := exists_nodePointCoordinates_add_of_unit_tangent D v w hv0 hlt hw hb hdt
  have hub := (residue_eq_zero_iff _).mp
    (node_add_unit_tangent_residues D v w u hv0 hlt hw hb hdt).2.2
  rw [hc, pow_one, nodePointParameter_negative D c₆ v hv0 (by omega) hb,
    nodePointParameter_positive D c₆ w (by omega) hw hd,
    nodePointParameter_positive D c₆ u (by omega) (by omega) (Or.inr hub),
    ← node_negative_positive_parameter_add D v w u hv0 hlt hw hb hdt]
  ring

/-- Equal opposite strict depths give the smooth output with exactly one carry. -/
theorem nodePointParameter_carry_opposite
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  classical
  have hc : nodePointCarry D P Q = 1 := by
    rw [nodePointCarry, nodePointLabel_val_positive D v (by omega) (Or.inr hb),
      nodePointLabel_val_negative D w (by omega) (by omega) hd]
    exact ite_eq_left (by omega)
  rw [hc, pow_one, nodePointParameter_positive D c₆ v hv0 (by omega) (Or.inr hb),
    nodePointParameter_negative D c₆ w (by omega) (by omega) hd,
    nodePointParameter_smooth D c₆ ⟨P + Q, v.smooth_add_of_opposite D w hv0 hv he hb hd⟩,
    ← node_opposite_parameter_smooth D v w hv0 hv he hb hd]
  ring

/-- Two midpoint inputs give the smooth output with exactly one carry. -/
theorem nodePointParameter_carry_middle_middle (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  classical
  have hn := D.depth_pos
  have hc : nodePointCarry D P Q = 1 := by
    rw [nodePointCarry, nodePointLabel_val_positive D v (by omega) (Or.inl hv),
      nodePointLabel_val_positive D w (by omega) (Or.inl hw)]
    exact ite_eq_left (by omega)
  rw [hc, pow_one,
    nodePointParameter_positive D c₆ v (by omega) (by omega) (Or.inl hv),
    nodePointParameter_positive D c₆ w (by omega) (by omega) (Or.inl hw),
    nodePointParameter_smooth D c₆ ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩]
  exact node_middle_parameter_smooth D v w hv hw c₆ h6

end FLT.Mazur
