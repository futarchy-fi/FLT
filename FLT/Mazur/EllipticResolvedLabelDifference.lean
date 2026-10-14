/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentDifference
public import FLT.Mazur.EllipticNodeLabelHom
public import FLT.Mazur.EllipticNodeLabelDecode

/-!
# Equality and arbitrary translation within a resolved component

Classify bounded primitive witnesses by their proved additive labels. Within
any one label, equality of resolved specializations is precisely the E₁
relation. Consequently translation by any generic point preserves and reflects
that equality, without restrictions on the output component or slope chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Equal labels allow the E₁ difference test on every actual resolved component. -/
theorem resolvedSplitSmoothPoint_eq_iff_difference_of_label_eq
    (hl : nodePointLabel D P = nodePointLabel D Q) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      InfinityReduction A W (P - Q) := by
  by_cases hp : SmoothReduction A W P
  · have hq := (nodePointLabel_eq_zero_iff D Q).mp
      (hl.symm.trans ((nodePointLabel_eq_zero_iff D P).mpr hp))
    exact resolvedSplitSmoothPoint_e0_eq_iff_difference A D ⟨P, hp⟩ ⟨Q, hq⟩
  have hq : ¬ SmoothReduction A W Q := by
    intro hq
    exact hp ((nodePointLabel_eq_zero_iff D P).mp
      (hl.trans ((nodePointLabel_eq_zero_iff D Q).mpr hq)))
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  rw [nodePointLabel_eq_of_coordinates D v, nodePointLabel_eq_of_coordinates D w] at hl
  have he := nodeBranchLabel_eq_imp_depth D.depth_pos hv hw v.b w.b hl
  by_cases hm : 2 * v.depth = n
  · exact resolvedSplitSmoothPoint_middle_eq_iff_difference A D v w hm (by omega)
  have hk := v.depth_pos_of_not_smooth D hp
  by_cases hb : v.b ∈ maximalIdeal A
  · have hd := (nodeBranchLabel_decode_positive D.depth_pos hk hv hw w.b
      (hl.symm.trans (nodeBranchLabel_of_mem n v.depth hb))).2
    exact resolvedSplitSmoothPoint_positive_eq_iff_difference A D v w hk (by omega) he.symm hb
      (hd.resolve_left hm)
  · have hu : IsUnit v.b := not_not.mp hb
    have hd := (nodeBranchLabel_decode_negative D.depth_pos hk (by omega) hw w.b
      (hl.symm.trans (nodeBranchLabel_eq_neg_of_unit n v.depth hu))).2
    exact resolvedSplitSmoothPoint_negative_eq_iff_difference A D v w hk (by omega) he.symm hu hd

/-- Any generic translator preserves and detects equality between inputs with the same label. -/
theorem resolvedSplitSmoothPoint_translation_eq_iff_of_label_eq
    (hl : nodePointLabel D P = nodePointLabel D Q)
    (T : (W.map (algebraMap A K)).toProjective.Point) :
    resolvedSplitSmoothPoint A D (P + T) = resolvedSplitSmoothPoint A D (Q + T) ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q := by
  have hs : nodePointLabel D (P + T) = nodePointLabel D (Q + T) := by
    rw [nodePointLabel_add, nodePointLabel_add, hl]
  rw [resolvedSplitSmoothPoint_eq_iff_difference_of_label_eq A D hs,
    resolvedSplitSmoothPoint_eq_iff_difference_of_label_eq A D hl, add_sub_add_right_eq_sub]

/-- Actual addition respects resolved equality on both pairs of equal-label inputs. -/
theorem resolvedSplitSmoothPoint_add_eq_of_label_eq
    {P' Q' : (W.map (algebraMap A K)).toProjective.Point}
    (hp : nodePointLabel D P = nodePointLabel D P')
    (hq : nodePointLabel D Q = nodePointLabel D Q')
    (ep : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D P')
    (eq : resolvedSplitSmoothPoint A D Q = resolvedSplitSmoothPoint A D Q') :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D (P' + Q') := by
  have e₁ := (resolvedSplitSmoothPoint_translation_eq_iff_of_label_eq A D hp Q).mpr ep
  have e₂ := (resolvedSplitSmoothPoint_translation_eq_iff_of_label_eq A D hq P').mpr eq
  exact e₁.trans (by simpa only [add_comm] using e₂)

end FLT.Mazur.WeierstrassDividedDepth
