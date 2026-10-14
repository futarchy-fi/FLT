/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedDepthSeparation
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Arithmetic labels are separated by the actual resolved geometry

Equality of actual resolved smooth points implies equality of the additive
component labels. Primitive depths are separated by earlier divided charts;
at a common depth the vertical residue distinguishes the strict branches,
including the final odd chart. Original smooth reduction handles label zero.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Actual equality determines whether a point lies over the original smooth cubic locus. -/
theorem resolvedSplitSmoothPoint_smooth_iff_of_eq
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    SmoothReduction A W P ↔ SmoothReduction A W Q :=
  finitePointSpecialization_smooth_iff_of_eq A D.uniformizer_ne_zero
    (splitResolutionData A D) (n / 2) (le_refl _) P Q
    ((resolvedSplitSmoothPoint_eq_iff A D P Q).mp he)

/-- Primitive branch labels agree whenever their actual resolved points agree. -/
theorem resolvedSplitSmoothPoint_branchLabel_eq
    (v : NodePointCoordinates A W π P) (hv : v.depth ≤ n / 2)
    (w : NodePointCoordinates A W π Q) (hw : w.depth ≤ n / 2)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    nodeBranchLabel n v.depth v.b = nodeBranchLabel n w.depth w.b := by
  classical
  have hd := resolvedSplitSmoothPoint_depth_eq A D v hv w hw he
  have hb := (resolvedSplitSmoothPoint_primitive_residues A D v hv w hw he).2
  simp only [nodeBranchLabel, ← residue_eq_zero_iff, hd, hb]

/-- Equal actual resolved smooth specializations always have equal arithmetic labels. -/
theorem resolvedSplitSmoothPoint_label_eq
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    nodePointLabel D P = nodePointLabel D Q := by
  by_cases hp : SmoothReduction A W P
  · have hq := (resolvedSplitSmoothPoint_smooth_iff_of_eq A D he).mp hp
    exact ((nodePointLabel_eq_zero_iff D P).mpr hp).trans
      ((nodePointLabel_eq_zero_iff D Q).mpr hq).symm
  have hq : ¬ SmoothReduction A W Q :=
    fun h => hp ((resolvedSplitSmoothPoint_smooth_iff_of_eq A D he).mpr h)
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  obtain ⟨w, hw⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem Q hq
  rw [nodePointLabel_eq_of_coordinates D v, nodePointLabel_eq_of_coordinates D w]
  exact resolvedSplitSmoothPoint_branchLabel_eq A D v hv w hw he

end FLT.Mazur.WeierstrassDividedDepth
