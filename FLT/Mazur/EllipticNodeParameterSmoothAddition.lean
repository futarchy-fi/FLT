/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterEvaluation
public import FLT.Mazur.EllipticNodeNormalizedSmoothTranslation

/-!
# Global parameter multiplication under original smooth translation

The global parameter restricts to the original smooth character and
multiplies by that character under every original E₀ translation.
This settles all smooth-input cases of the carry law.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)

/-- Original smooth points multiply according to the actual smooth character. -/
theorem nodePointParameter_add_smooth (P Q : ellipticE0 A W) :
    nodePointParameter D c₆ (P.val + Q.val) =
      nodePointParameter D c₆ P.val * nodePointParameter D c₆ Q.val := by
  classical
  rw [show P.val + Q.val = (P + Q).val from rfl]
  rw [nodePointParameter_smooth, nodePointParameter_smooth, nodePointParameter_smooth, map_add]
  rfl

/-- Every original smooth translation multiplies the global parameter. -/
theorem nodePointParameter_smooth_translate
    (P : (W.map (algebraMap A K)).toProjective.Point) (T : ellipticE0 A W) :
    nodePointParameter D c₆ (P + T.val) =
      nodePointParameter D c₆ P * nodePointParameter D c₆ T.val := by
  classical
  by_cases hp : SmoothReduction A W P
  · exact nodePointParameter_add_smooth D c₆ ⟨P, hp⟩ T
  have hs : ¬ SmoothReduction A W (P + T.val) := by
    intro hs
    apply hp
    apply (nodePointLabel_eq_zero_iff D P).mp
    rw [← nodePointLabel_add_smooth_right D P T.val T.property]
    exact (nodePointLabel_eq_zero_iff D _).mpr hs
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨u, hu⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem (P + T.val) hs
  have hv0 := v.depth_pos_of_not_smooth D hp
  have hu0 := u.depth_pos_of_not_smooth D hs
  have hl := node_smooth_translate_branchLabel D T v u
  have hd := nodeBranchLabel_eq_imp_depth D.depth_pos hu hv u.b v.b hl
  rw [nodePointParameter_smooth D c₆ T]
  by_cases hm : 2 * v.depth = n
  · rw [nodePointParameter_positive D c₆ v hv0 hv (Or.inl hm),
      nodePointParameter_positive D c₆ u hu0 hu (Or.inl (by omega))]
    exact node_middle_parameter_smooth_translate D T v u hm hu
  by_cases hb : v.b ∈ maximalIdeal A
  · have hub := (nodeBranchLabel_decode_positive D.depth_pos hv0 hv hu u.b
      (hl.trans (nodeBranchLabel_of_mem n v.depth hb))).2.resolve_left hm
    rw [nodePointParameter_positive D c₆ v hv0 hv (Or.inr hb),
      nodePointParameter_positive D c₆ u hu0 hu (Or.inr hub)]
    exact node_positive_parameter_smooth_translate D T v u hv0 (by omega) hu hb
  · have hb' : IsUnit v.b := not_not.mp hb
    have hub := (nodeBranchLabel_decode_negative D.depth_pos hv0 (by omega) hu u.b
      (hl.trans (nodeBranchLabel_eq_neg_of_unit n v.depth hb'))).2
    rw [nodePointParameter_negative D c₆ v hv0 (by omega) hb',
      nodePointParameter_negative D c₆ u hu0 (by omega) hub,
      node_negative_parameter_smooth_translate D T v u hv0 (by omega) hu hb', mul_assoc]

/-- A smooth input never creates a component carry. -/
theorem nodePointCarry_smooth_right
    (P : (W.map (algebraMap A K)).toProjective.Point) (T : ellipticE0 A W) :
    nodePointCarry D P T.val = 0 := by
  have : NeZero n := ⟨Nat.ne_of_gt D.depth_pos⟩
  have ht := (nodePointLabel_eq_zero_iff D T.val).mpr T.property
  have hp := (nodePointLabel D P).val_lt
  simp only [nodePointCarry, ht, ZMod.val_zero, Nat.add_zero, not_le.mpr hp, ite_false]

/-- The global carry formula holds whenever the second input is smooth. -/
theorem nodePointParameter_carry_smooth_right
    (P : (W.map (algebraMap A K)).toProjective.Point) (T : ellipticE0 A W) :
    nodePointParameter D c₆ P * nodePointParameter D c₆ T.val =
      nodeWrapParameter W c₆ ^ nodePointCarry D P T.val *
        nodePointParameter D c₆ (P + T.val) := by
  rw [nodePointCarry_smooth_right D P T, pow_zero, one_mul,
    nodePointParameter_smooth_translate D c₆ P T]

end FLT.Mazur
