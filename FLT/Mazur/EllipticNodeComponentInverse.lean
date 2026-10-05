/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Inverse compatibility for actual nodal component labels

Construct primitive coordinates of the actual inverse point from the
Weierstrass inverse formula. This proves sign compatibility for every generic
point, including the smooth locus and the even middle component.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)

include D in
/-- An inverse point has a primitive witness at the same depth and with opposite label. -/
theorem exists_nodePointCoordinates_inverse
    {P : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) (hk : v.depth ≤ n / 2) :
    ∃ w : NodePointCoordinates A W π (-P), w.depth = v.depth ∧
      nodeBranchLabel n w.depth w.b = -nodeBranchLabel n v.depth v.b := by
  obtain ⟨c, hc, hce⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  let b' := -v.b - W.a₁ * v.a - c
  have hy : (W.map (algebraMap A K)).toAffine.negY
      ((π ^ v.depth * v.a : A) : K) ((π ^ v.depth * v.b : A) : K) =
      ((π ^ v.depth * b' : A) : K) := by
    change (W.toAffine.map (algebraMap A K)).negY
      (algebraMap A K (π ^ v.depth * v.a))
      (algebraMap A K (π ^ v.depth * v.b)) = _
    rw [Affine.map_negY, node_negY_scaled W π v.depth v.a v.b c hce]
    rfl
  have hs : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ v.depth * v.a : A) : K) ((π ^ v.depth * b' : A) : K) := by
    rw [← hy]
    exact (Affine.nonsingular_neg _ _).mpr v.nonsingular
  have hr : -P = Affine.Point.toProjective (.some _ _ hs) := by
    conv_lhs => rw [v.represents]
    rw [← toProjective_neg, Affine.Point.neg_some]
    apply congrArg Affine.Point.toProjective
    simp only [Affine.Point.some.injEq]
    exact ⟨trivial, hy⟩
  refine ⟨⟨v.depth, v.a, b', node_neg_primitive W hc v.primitive, hs, hr⟩, rfl, ?_⟩
  exact nodeBranchLabel_neg W π D.uniformizer_ne_zero D.maximalIdeal_eq n v.depth hk
    D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem v.a v.b c hc v.primitive v.equation

/-- Negation in the actual generic group negates its component label. -/
@[simp] theorem nodePointLabel_neg (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (-P) = -nodePointLabel D P := by
  classical
  by_cases hp : SmoothReduction A W P
  · rw [(nodePointLabel_eq_zero_iff D P).mpr hp,
      (nodePointLabel_eq_zero_iff D (-P)).mpr (hp.neg A W), neg_zero]
  · obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
    obtain ⟨w, _, hw⟩ := exists_nodePointCoordinates_inverse D v hv
    rw [nodePointLabel_eq_of_coordinates D w, nodePointLabel_eq_of_coordinates D v]
    exact hw

end FLT.Mazur
