/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodePointParameter
public import FLT.Mazur.EllipticResolvedGeometricLabel
public import FLT.Mazur.EllipticResolvedLabelDifference

/-!
# A global equality test by the original label and normalized parameter

The normalized parameter is constant on actual resolved specialization.
Together with the proved label it detects that specialization, including
the midpoint, the final odd branches and the original smooth component.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Equal actual resolved points have the same original global parameter. -/
theorem resolvedSplitSmoothPoint_parameter_eq
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    nodePointParameter D c₆ P = nodePointParameter D c₆ Q := by
  classical
  have hs := resolvedSplitSmoothPoint_smooth_iff_of_eq A D he
  by_cases hp : SmoothReduction A W P
  · have hq := hs.mp hp
    rw [nodePointParameter_smooth D c₆ ⟨P, hp⟩, nodePointParameter_smooth D c₆ ⟨Q, hq⟩]
    exact congrArg (fun z => (Additive.toMul z).val)
      ((resolvedSplitSmoothPoint_e0_character_eq_iff A D ⟨P, hp⟩ ⟨Q, hq⟩).mp he)
  have hq : ¬ SmoothReduction A W Q := fun h => hp (hs.mpr h)
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  rw [nodePointParameter_of_coordinates D c₆ v hp, nodePointParameter_of_coordinates D c₆ w hq]
  obtain ⟨ha, hb⟩ := resolvedSplitSmoothPoint_primitive_residues A D v hv w hw he
  exact nodeCoordinateParameter_eq_of_residues c₆ v w
    (resolvedSplitSmoothPoint_depth_eq A D v hv w hw he) ha hb

/-- Label and original parameter together detect equality in the whole actual resolved fiber. -/
theorem resolvedSplitSmoothPoint_eq_iff_label_parameter (h6 : W.a₆ = π ^ n * c₆) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      nodePointLabel D P = nodePointLabel D Q ∧ nodePointParameter D c₆ P =
        nodePointParameter D c₆ Q := by
  classical
  refine ⟨fun he => ⟨resolvedSplitSmoothPoint_label_eq A D he,
    resolvedSplitSmoothPoint_parameter_eq A D c₆ he⟩, ?_⟩
  rintro ⟨hl, hpq⟩
  by_cases hp : SmoothReduction A W P
  · have hq := (nodePointLabel_eq_zero_iff D Q).mp
      (hl.symm.trans ((nodePointLabel_eq_zero_iff D P).mpr hp))
    apply (resolvedSplitSmoothPoint_e0_character_eq_iff A D ⟨P, hp⟩ ⟨Q, hq⟩).mpr
    rw [nodePointParameter_smooth D c₆ ⟨P, hp⟩,
      nodePointParameter_smooth D c₆ ⟨Q, hq⟩] at hpq
    exact congrArg Additive.ofMul (Units.ext hpq)
  have hq : ¬ SmoothReduction A W Q := by
    intro hq
    exact hp ((nodePointLabel_eq_zero_iff D P).mp
      (hl.trans ((nodePointLabel_eq_zero_iff D Q).mpr hq)))
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  rw [nodePointParameter_of_coordinates D c₆ v hp,
    nodePointParameter_of_coordinates D c₆ w hq] at hpq
  rw [nodePointLabel_eq_of_coordinates D v, nodePointLabel_eq_of_coordinates D w] at hl
  have he := nodeBranchLabel_eq_imp_depth D.depth_pos hv hw v.b w.b hl
  have ht := nodeWrapParameter_ne_zero D c₆ h6
  by_cases hm : 2 * v.depth = n
  · have hmw : 2 * w.depth = n := by omega
    simp only [nodeCoordinateParameter, hm, hmw, true_or, ite_true] at hpq
    rw [node_middle_parameter_transition D v hm c₆ h6,
      node_middle_parameter_transition D w hmw c₆ h6] at hpq
    exact (resolvedSplitSmoothPoint_middle_character_eq_iff A D P Q v w hm hmw).mpr
      ((nodeNegativeParameter_eq_iff D v w).mp (mul_left_cancel₀ ht hpq))
  have hk := v.depth_pos_of_not_smooth D hp
  by_cases hb : v.b ∈ maximalIdeal A
  · have hd := (nodeBranchLabel_decode_positive D.depth_pos hk hv hw w.b
      (hl.symm.trans (nodeBranchLabel_of_mem n v.depth hb))).2.resolve_left hm
    simp only [nodeCoordinateParameter, hb, hd, or_true, ite_true] at hpq
    exact (resolvedSplitSmoothPoint_strict_positive_eq_iff A D v.depth hk (by omega)
      P Q v rfl w he.symm hb hd).mpr ((nodePositiveParameter_eq_iff D v w).mp hpq)
  · have hu : IsUnit v.b := not_not.mp hb
    have hd := (nodeBranchLabel_decode_negative D.depth_pos hk (by omega) hw w.b
      (hl.symm.trans (nodeBranchLabel_eq_neg_of_unit n v.depth hu))).2
    have hmw : ¬ 2 * w.depth = n := by omega
    have hd' : w.b ∉ maximalIdeal A := fun h => h hd
    simp only [nodeCoordinateParameter, hm, hmw, hb, hd', or_self, ite_false] at hpq
    exact (resolvedSplitSmoothPoint_strict_negative_eq_iff A D v.depth hk (by omega)
      P Q v rfl w he.symm hu hd).mpr
      ((nodeNegativeParameter_eq_iff D v w).mp (mul_left_cancel₀ ht hpq))

end FLT.Mazur.WeierstrassDividedDepth
