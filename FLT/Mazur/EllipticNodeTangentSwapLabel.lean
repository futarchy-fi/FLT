/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTangentSwap
public import FLT.Mazur.EllipticNodeGenericNonsingular
public import FLT.Mazur.EllipticComponentVariableChange

/-!
# Tangent exchange negates actual component labels

The integral projective variable-change map sends the swapped model back to
the original model. Its coordinate shear exchanges the tangent branches,
so its action on the canonical component labels is multiplication by -1.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  [(W.map (algebraMap A K)).IsElliptic]

include D in
/-- The actual tangent-exchanging coordinate map carries primitive witnesses and negates labels. -/
theorem exists_nodePointCoordinates_tangentSwap
    {P : ((nodeTangentSwap W • W).map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A (nodeTangentSwap W • W) π P) (hk : v.depth ≤ n / 2) :
    ∃ w : NodePointCoordinates A W π
      (integralProjectiveVariableChange A W (nodeTangentSwap W) P),
      w.depth = v.depth ∧ nodeBranchLabel n w.depth w.b = -nodeBranchLabel n v.depth v.b := by
  let V := nodeTangentSwap W • W
  let b := v.b - W.a₁ * v.a
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := nodeTangentSwap_coefficients W
  have hb : b = v.b + V.a₁ * v.a := by dsimp [b, V]; rw [h₁]; ring
  have he : W.toAffine.Equation (π ^ v.depth * v.a) (π ^ v.depth * b) := by
    have h := (Affine.equation_iff _ _).mp v.equation
    rw [h₁, h₂, h₃, h₄, h₆] at h
    rw [Affine.equation_iff]
    dsimp [b]
    linear_combination h
  have hs := D.generic_nonsingular he
  have hr : integralProjectiveVariableChange A W (nodeTangentSwap W) P =
      Affine.Point.toProjective (.some _ _ hs) := by
    conv_lhs => rw [v.represents]
    change (((Projective.Point.toAffineAddEquiv _).trans
      (integralAffineVariableChange A W (nodeTangentSwap W))).trans
      (Projective.Point.toAffineAddEquiv _).symm)
      ((Projective.Point.toAffineAddEquiv _).symm (.some _ _ v.nonsingular)) = _
    simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    simp only [integralAffineVariableChange, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Projective.Point.toAffineAddEquiv_symm_apply]
    apply congrArg Affine.Point.toProjective
    simp only [Affine.Point.some.injEq]
    constructor
    · simp [nodeTangentSwap, VariableChange.map]
    · simp [nodeTangentSwap, VariableChange.map, b]
      ring
  refine ⟨⟨v.depth, v.a, b, ?_, hs, hr⟩, rfl, ?_⟩
  · rw [hb]
    exact nodeTangentSwap_primitive V v.primitive
  · change nodeBranchLabel n v.depth b = _
    rw [hb]
    exact nodeTangentSwap_branchLabel V (D.tangentSwap W) hk v.a v.b v.primitive v.equation

/-- The actual projective variable-change equivalence negates signed point labels. -/
theorem nodePointLabel_tangentSwap
    (P : ((nodeTangentSwap W • W).map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (integralProjectiveVariableChange A W (nodeTangentSwap W) P) =
      -nodePointLabel (D.tangentSwap W) P := by
  by_cases hp : SmoothReduction A (nodeTangentSwap W • W) P
  · rw [(nodePointLabel_eq_zero_iff (D.tangentSwap W) P).mpr hp,
      (nodePointLabel_eq_zero_iff D _).mpr
        ((integralProjectiveVariableChange_smooth A W (nodeTangentSwap W) P).mpr hp), neg_zero]
  · obtain ⟨v, hv⟩ := exists_nodePointCoordinates A (nodeTangentSwap W • W) π
      D.maximalIdeal_eq n (D.tangentSwap W).a₃_mem (D.tangentSwap W).a₄_mem
      (D.tangentSwap W).a₆_not_mem P hp
    obtain ⟨w, _, hw⟩ := exists_nodePointCoordinates_tangentSwap D v hv
    rw [nodePointLabel_eq_of_coordinates D w,
      nodePointLabel_eq_of_coordinates (D.tangentSwap W) v]
    exact hw

/-- The actual component equivalence induced by tangent exchange acts by negation on labels. -/
theorem nodeComponentLabel_tangentSwap (c : EllipticComponentQuotient A (nodeTangentSwap W • W)) :
    nodeComponentLabel D (integralComponentVariableChange A W (nodeTangentSwap W) c) =
      -nodeComponentLabel (D.tangentSwap W) c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A (nodeTangentSwap W • W) c
  rw [integralComponentVariableChange_mk, nodeComponentLabel_mk, nodeComponentLabel_mk]
  exact nodePointLabel_tangentSwap D P

end FLT.Mazur
