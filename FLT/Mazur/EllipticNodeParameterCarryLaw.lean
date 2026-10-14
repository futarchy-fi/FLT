/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterMixedAddition
public import FLT.Mazur.EllipticNodeParameterSameBranch
public import FLT.Mazur.EllipticNodeParameterSmoothAddition

/-!
# The unrestricted original parameter carry law

For every pair of original generic points, their parameters multiply to
the parameter of their actual sum, times the original period coefficient
exactly when the nonnegative labels cross the full component period.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- The global carry formula is unchanged when the inputs are exchanged. -/
theorem nodePointParameter_carry_swap
    (h : nodePointParameter D c₆ Q * nodePointParameter D c₆ P =
      nodeWrapParameter W c₆ ^ nodePointCarry D Q P * nodePointParameter D c₆ (Q + P)) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  simpa only [nodePointCarry_comm D Q P, add_comm Q P,
    mul_comm (nodePointParameter D c₆ Q) (nodePointParameter D c₆ P)] using h

/-- Ordered bounded primitive witnesses satisfy the carry law on every nodal component. -/
theorem nodePointParameter_carry_of_depth_le (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth) (hle : v.depth ≤ w.depth)
    (hv : v.depth ≤ n / 2) (hw : w.depth ≤ n / 2) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  by_cases hvm : 2 * v.depth = n
  · exact nodePointParameter_carry_middle_middle D c₆ h6 v w hvm (by omega)
  by_cases hwm : 2 * w.depth = n
  · by_cases hb : v.b ∈ maximalIdeal A
    · exact nodePointParameter_carry_positive_unit_lt D c₆ h6 v w hv0 (by omega) hw
        hb (w.units_of_middle D hwm).1
    · exact nodePointParameter_carry_negative_positive_lt D c₆ v w hv0 (by omega) hw
        (not_not.mp hb) (Or.inl hwm)
  by_cases hb : v.b ∈ maximalIdeal A
  · by_cases hd : w.b ∈ maximalIdeal A
    · exact nodePointParameter_carry_positive_positive D c₆ h6 v w hv0 hw0
        (by omega) (by omega) hb hd
    · rcases eq_or_lt_of_le hle with he | he
      · exact nodePointParameter_carry_opposite D c₆ v w hv0 (by omega) he hb (not_not.mp hd)
      · exact nodePointParameter_carry_positive_unit_lt D c₆ h6 v w hv0 he hw
          hb (not_not.mp hd)
  · by_cases hd : w.b ∈ maximalIdeal A
    · rcases eq_or_lt_of_le hle with he | he
      · exact nodePointParameter_carry_swap D c₆
          (nodePointParameter_carry_opposite D c₆ w v hw0 (by omega) he.symm hd
            (not_not.mp hb))
      · exact nodePointParameter_carry_negative_positive_lt D c₆ v w hv0 he hw
          (not_not.mp hb) (Or.inr hd)
    · exact nodePointParameter_carry_negative_negative D c₆ h6 v w hv0 hw0
        (by omega) (by omega) (not_not.mp hb) (not_not.mp hd)

/-- Every pair of original generic points satisfies the coefficient-dependent carry law. -/
theorem nodePointParameter_carry (h6 : W.a₆ = π ^ n * c₆)
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ Q =
      nodeWrapParameter W c₆ ^ nodePointCarry D P Q * nodePointParameter D c₆ (P + Q) := by
  by_cases hq : SmoothReduction A W Q
  · exact nodePointParameter_carry_smooth_right D c₆ P ⟨Q, hq⟩
  by_cases hp : SmoothReduction A W P
  · exact nodePointParameter_carry_swap D c₆
      (nodePointParameter_carry_smooth_right D c₆ Q ⟨P, hp⟩)
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  have hv0 := v.depth_pos_of_not_smooth D hp
  have hw0 := w.depth_pos_of_not_smooth D hq
  rcases le_total v.depth w.depth with h | h
  · exact nodePointParameter_carry_of_depth_le D c₆ h6 v w hv0 hw0 h hv hw
  · exact nodePointParameter_carry_swap D c₆
      (nodePointParameter_carry_of_depth_le D c₆ h6 w v hw0 hv0 h hw hv)

/-- The same law holds in residue-field units, with no zero denominators. -/
theorem nodePointParameterUnit_carry (h6 : W.a₆ = π ^ n * c₆)
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointParameterUnit D c₆ h6 P * nodePointParameterUnit D c₆ h6 Q =
      nodeWrapParameterUnit D c₆ h6 ^ nodePointCarry D P Q *
        nodePointParameterUnit D c₆ h6 (P + Q) := by
  apply Units.ext
  exact nodePointParameter_carry D c₆ h6 P Q

end FLT.Mazur
