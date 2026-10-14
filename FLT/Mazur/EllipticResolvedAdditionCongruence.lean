/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedGeometricLabel
public import FLT.Mazur.EllipticResolvedLabelDifference

/-!
# Unrestricted arithmetic congruence of actual resolved smooth points

Equality in the actual resolved smooth fiber is precisely the E₁ difference
relation. No equality of labels is assumed. Consequently every generic
translation preserves and reflects equality, and addition, inverse and
integer multiplication respect specialization equality.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Equality of actual resolved points is exactly the unrestricted E₁ difference relation. -/
theorem resolvedSplitSmoothPoint_eq_iff_difference :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      InfinityReduction A W (P - Q) := by
  constructor
  · intro he
    exact (resolvedSplitSmoothPoint_eq_iff_difference_of_label_eq A D
      (resolvedSplitSmoothPoint_label_eq A D he)).mp he
  · intro hi
    have hz := (nodePointLabel_eq_zero_iff D (P - Q)).mpr (hi.smooth A W)
    have hl : nodePointLabel D P = nodePointLabel D Q := by
      change nodePointLabelHom D (P - Q) = 0 at hz
      rw [map_sub, sub_eq_zero] at hz
      exact hz
    exact (resolvedSplitSmoothPoint_eq_iff_difference_of_label_eq A D hl).mpr hi

/-- Any generic translation preserves and reflects actual resolved equality. -/
theorem resolvedSplitSmoothPoint_translation_eq_iff
    (T : (W.map (algebraMap A K)).toProjective.Point) :
    resolvedSplitSmoothPoint A D (P + T) = resolvedSplitSmoothPoint A D (Q + T) ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q := by
  rw [resolvedSplitSmoothPoint_eq_iff_difference,
    resolvedSplitSmoothPoint_eq_iff_difference, add_sub_add_right_eq_sub]

/-- Addition respects both unrestricted actual specialization equalities. -/
theorem resolvedSplitSmoothPoint_add_eq
    {P' Q' : (W.map (algebraMap A K)).toProjective.Point}
    (hp : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D P')
    (hq : resolvedSplitSmoothPoint A D Q = resolvedSplitSmoothPoint A D Q') :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D (P' + Q') := by
  exact resolvedSplitSmoothPoint_add_eq_of_label_eq A D
    (resolvedSplitSmoothPoint_label_eq A D hp) (resolvedSplitSmoothPoint_label_eq A D hq) hp hq

/-- Negation preserves and reflects actual resolved equality. -/
theorem resolvedSplitSmoothPoint_neg_eq_iff :
    resolvedSplitSmoothPoint A D (-P) = resolvedSplitSmoothPoint A D (-Q) ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q := by
  rw [resolvedSplitSmoothPoint_eq_iff_difference, resolvedSplitSmoothPoint_eq_iff_difference]
  rw [show -P - -Q = -(P - Q) by abel]
  change -(P - Q) ∈ ellipticE1 A W ↔ P - Q ∈ ellipticE1 A W
  exact (ellipticE1 A W).neg_mem_iff

/-- Natural multiplication respects actual resolved equality. -/
theorem resolvedSplitSmoothPoint_nsmul_eq (m : ℕ)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    resolvedSplitSmoothPoint A D (m • P) = resolvedSplitSmoothPoint A D (m • Q) := by
  rw [resolvedSplitSmoothPoint_eq_iff_difference] at he ⊢
  change m • P - m • Q ∈ ellipticE1 A W
  rw [← nsmul_sub]
  exact (ellipticE1 A W).nsmul_mem he m

/-- Integer multiplication respects actual resolved equality. -/
theorem resolvedSplitSmoothPoint_zsmul_eq (m : ℤ)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    resolvedSplitSmoothPoint A D (m • P) = resolvedSplitSmoothPoint A D (m • Q) := by
  rw [resolvedSplitSmoothPoint_eq_iff_difference] at he ⊢
  change m • P - m • Q ∈ ellipticE1 A W
  rw [← zsmul_sub]
  exact (ellipticE1 A W).zsmul_mem he m

end FLT.Mazur.WeierstrassDividedDepth
