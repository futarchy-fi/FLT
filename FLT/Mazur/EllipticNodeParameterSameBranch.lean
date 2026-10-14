/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterEvaluation
public import FLT.Mazur.EllipticNodeNormalizedMiddleAddition

/-!
# The global carry law on each strict branch

Positive inputs never cross the full period. Negative inputs always cross
it once. The actual output may be on either branch or at the midpoint;
its oriented formula supplies precisely the required period coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Any two points on the same strict branch have nonsmooth original sum. -/
theorem node_same_strict_branch_not_smooth
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n)
    (hb : v.b ∈ maximalIdeal A ↔ w.b ∈ maximalIdeal A) :
    ¬ SmoothReduction A W (P + Q) := by
  rcases lt_trichotomy v.depth w.depth with h | h | h
  · exact v.not_smooth_add D w hv0 h (by omega)
  · exact v.not_smooth_add_of_same_branch D w hv0 hv h hb
  · simpa only [add_comm] using w.not_smooth_add D v hw0 h (by omega)

/-- Two strict positive inputs obey the global formula with zero carry. -/
theorem nodePointParameter_carry_positive_positive (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  have hc : nodePointCarry D P Q = 0 := by
    rw [nodePointCarry, nodePointLabel_val_positive D v (by omega) (Or.inr hb),
      nodePointLabel_val_positive D w (by omega) (Or.inr hd)]
    exact ite_eq_right (by omega)
  rw [hc, pow_zero, one_mul,
    nodePointParameter_positive D c₆ v hv0 (by omega) (Or.inr hb),
    nodePointParameter_positive D c₆ w hw0 (by omega) (Or.inr hd)]
  have hs := node_same_strict_branch_not_smooth D v w hv0 hw0 hv hw (by simp [hb, hd])
  obtain ⟨u, hu⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem (P + Q) hs
  have hu0 := u.depth_pos_of_not_smooth D hs
  by_cases hm : 2 * u.depth = n
  · rw [nodePointParameter_positive D c₆ u hu0 hu (Or.inl hm)]
    exact node_positive_parameter_middle D v w u hv0 hw0 hv hw hm hb hd c₆ h6
  by_cases hf : u.b ∈ maximalIdeal A
  · rw [nodePointParameter_positive D c₆ u hu0 hu (Or.inr hf)]
    exact node_positive_parameter_add D v w u hv0 hw0 hv hw (by omega) hb hd hf
  · rw [nodePointParameter_negative D c₆ u hu0 (by omega) (not_not.mp hf)]
    exact node_positive_parameter_wrap D v w u hv0 hw0 hu0 hv hw (by omega)
      hb hd (not_not.mp hf) c₆ h6

/-- Two strict negative inputs obey the global formula with one carry. -/
theorem nodePointParameter_carry_negative_negative (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n)
    (hb : IsUnit v.b) (hd : IsUnit w.b) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  have hc : nodePointCarry D P Q = 1 := by
    rw [nodePointCarry, nodePointLabel_val_negative D v hv0 hv hb,
      nodePointLabel_val_negative D w hw0 hw hd]
    exact ite_eq_left (by omega)
  rw [hc, pow_one, nodePointParameter_negative D c₆ v hv0 hv hb,
    nodePointParameter_negative D c₆ w hw0 hw hd]
  have hs := node_same_strict_branch_not_smooth D v w hv0 hw0 hv hw
    ⟨fun h => (h hb).elim, fun h => (h hd).elim⟩
  obtain ⟨u, hu⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem (P + Q) hs
  have hu0 := u.depth_pos_of_not_smooth D hs
  by_cases hm : 2 * u.depth = n
  · rw [nodePointParameter_middle_negative D c₆ h6 u hm,
      ← node_negative_parameter_middle D v w u hv0 hw0 hv hw hm hb hd c₆ h6]
    ring
  by_cases hf : u.b ∈ maximalIdeal A
  · rw [nodePointParameter_positive D c₆ u hu0 hu (Or.inr hf),
      ← node_negative_parameter_wrap D v w u hv0 hw0 hu0 hv hw (by omega) hb hd hf c₆ h6]
    ring
  · rw [nodePointParameter_negative D c₆ u hu0 (by omega) (not_not.mp hf),
      ← node_negative_parameter_add D v w u hv0 hw0 hu0 hv hw (by omega)
        hb hd (not_not.mp hf)]
    ring

end FLT.Mazur
