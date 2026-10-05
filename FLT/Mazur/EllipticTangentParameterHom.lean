/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNonsplitNodeParameter
public import FLT.Mazur.EllipticSplitNodeGroup
public import FLT.Mazur.EllipticSmoothPointChange

/-!
# The tangent parameter respects actual point addition

Over the quadratic tangent field, undoing the tangent shear identifies the
normalized equation with a split node. Composing this coordinate equivalence
with base change and the split-node parameter gives the tangent-ratio homomorphism.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

/-- The coordinate formula of the smooth-point homomorphism, without ellipticity. -/
theorem smoothPointChangeHom_some {k : Type*} [Field k] [DecidableEq k]
    (E : WeierstrassCurve k) (C : VariableChange k) {x y : k}
    (h : (C • E).toAffine.Nonsingular x y) :
    smoothPointChangeHom E C (.some x y h) =
      .some ((C.u : k) ^ 2 * x + C.r)
        ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
        ((variableChange_nonsingular E C x y).mpr h) := rfl

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]

local notation "L" => AdjoinRoot (nodeTangentPolynomial W)

/-- Undoing the tangent shear recovers the original normalized equation. -/
theorem nodeTangent_inverse_shear (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    (⟨1, 0, -AdjoinRoot.root (nodeTangentPolynomial W), 0⟩ : VariableChange L) •
        splitNodeCurve (algebraMap F L W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W)) =
      W.map (algebraMap F L) := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, splitNodeCurve, map_a₁, map_a₂, map_a₃, map_a₄,
    map_a₆, h3, h4, h6, map_zero, inv_one, Units.val_one, one_pow, one_mul,
    zero_mul, mul_zero, add_zero, sub_zero, neg_mul, neg_sq, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0)]
  · ring
  · linear_combination nodeTangentRoot_equation W

variable [DecidableEq F] [DecidableEq (AdjoinRoot (nodeTangentPolynomial W))]

/-- The actual smooth point equivalence from the tangent-field model to the split node. -/
noncomputable def nodeTangentToSplitEquiv (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    (W.map (algebraMap F L)).toAffine.Point ≃+
      (splitNodeCurve (algebraMap F L W.a₁ +
        2 * AdjoinRoot.root (nodeTangentPolynomial W))).toAffine.Point :=
  (Affine.Point.equivOfEq (nodeTangent_inverse_shear W h3 h4 h6).symm).trans
    (smoothPointChangeEquiv _ ⟨1, 0, -AdjoinRoot.root (nodeTangentPolynomial W), 0⟩)

/-- The tangent-ratio homomorphism obtained from the actual base-change and addition maps. -/
noncomputable def nodeTangentPointHom (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    W.toAffine.Point →+ Additive Lˣ :=
  (splitNodeParameterHom _).comp ((nodeTangentToSplitEquiv W h3 h4 h6).toAddMonoidHom.comp
    (Affine.Point.map (W' := W.toAffine) (Algebra.ofId F L)))

/-- The homomorphism computes the explicit ratio of the two tangent factors. -/
theorem nodeTangentPointHom_val (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (P : W.toAffine.Point) :
    ((Additive.toMul (nodeTangentPointHom W h3 h4 h6 P) : Lˣ) : L) =
      nodeTangentPointParameter W P := by
  cases P with
  | zero => simp only [← Affine.Point.zero_def, map_zero]; rfl
  | some x y h =>
    have hx : algebraMap F L x ≠ 0 := (map_ne_zero_iff _ (algebraMap F L).injective).mpr
      (normalized_nonsingular_x_ne_zero W h3 h4 h6 h)
    have hd := (nodeTangentPoint_factors_ne_zero W h3 h4 h6 h).2
    change (splitNodeParameterUnit _ ((nodeTangentToSplitEquiv W h3 h4 h6)
      (Affine.Point.map (W' := W.toAffine) (Algebra.ofId F L) (.some x y h))) : L) = _
    erw [Affine.Point.map_some]
    unfold nodeTangentToSplitEquiv
    erw [AddEquiv.trans_apply, Affine.Point.equivOfEq_some]
    simp only [splitNodeParameterUnit, Units.val_mk0]
    unfold smoothPointChangeEquiv
    erw [AddEquiv.ofBijective_apply]
    erw [smoothPointChangeHom_some]
    simp only [Units.val_one, one_pow, one_mul, add_zero, neg_mul, ← sub_eq_add_neg]
    change ((algebraMap F L y - AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap F L x) /
        algebraMap F L x) / (((algebraMap F L y -
          AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap F L x) / algebraMap F L x) +
            (algebraMap F L W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W))) = _
    have he : (algebraMap F L y - AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap F L x) /
        algebraMap F L x + (algebraMap F L W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W)) =
        (algebraMap F L y + (algebraMap F L W.a₁ + AdjoinRoot.root (nodeTangentPolynomial W)) *
          algebraMap F L x) / algebraMap F L x := by field_simp; ring
    rw [he]
    change _ = _ / _
    field_simp

omit [DecidableEq (AdjoinRoot (nodeTangentPolynomial W))] in
/-- The explicit tangent ratio multiplies under the actual addition law. -/
theorem nodeTangentPointParameter_add (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    (P Q : W.toAffine.Point) : nodeTangentPointParameter W (P + Q) =
      nodeTangentPointParameter W P * nodeTangentPointParameter W Q := by
  classical
  rw [← nodeTangentPointHom_val W h3 h4 h6, map_add]
  exact congrArg₂ (· * ·) (nodeTangentPointHom_val W h3 h4 h6 P)
    (nodeTangentPointHom_val W h3 h4 h6 Q)

end FLT.Mazur
