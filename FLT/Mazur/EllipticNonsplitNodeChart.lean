/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNonsplitNodeGroup
public import Mathlib.Data.Fintype.Option

/-!
# Counting the smooth points of a nonsplit node

The slope chart has no omitted ground-field slope: the two excluded
geometric slopes lie in the quadratic tangent field. Adding infinity
therefore gives a bijection with `Option F` and cardinality |F|+1.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]

/-- The affine slope chart, completed by the point at infinity. -/
noncomputable def nonsplitNodeChart
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) : Option F → W.toAffine.Point
  | none => 0
  | some t => .some _ _ (nonsplitNode_nonsingular_slope W h3 h4 h6 t)

/-- A smooth point gives its slope, or the extra infinity parameter. -/
def nonsplitNodeSlope : W.toAffine.Point → Option F
  | .zero => none
  | .some x y _ => some (y / x)

/-- Reading the slope of a chart point recovers its parameter. -/
theorem nonsplitNodeSlope_chart
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (t : Option F) :
    nonsplitNodeSlope W (nonsplitNodeChart W h3 h4 h6 t) = t := by
  cases t with
  | none => rfl
  | some t =>
    simp only [nonsplitNodeChart, nonsplitNodeSlope,
      mul_div_cancel_right₀ _ (nonsplit_tangent_value_ne_zero W t)]

/-- The slope chart recovers every smooth point. -/
theorem nonsplitNodeChart_slope
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (P : W.toAffine.Point) :
    nonsplitNodeChart W h3 h4 h6 (nonsplitNodeSlope W P) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    exact (Affine.Point.some.injEq _ _ _ _ _ _).mpr
      (normalized_coordinates_slope W h3 h4 h6 h)

/-- Smooth points of a normalized nonsplit node are the ground-field slopes and infinity. -/
noncomputable def nonsplitNodeChartEquiv
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) : Option F ≃ W.toAffine.Point where
  toFun := nonsplitNodeChart W h3 h4 h6
  invFun := nonsplitNodeSlope W
  left_inv := nonsplitNodeSlope_chart W h3 h4 h6
  right_inv := nonsplitNodeChart_slope W h3 h4 h6

/-- A normalized nonsplit node over a finite field has |F|+1 smooth points. -/
theorem nonsplitNodePoint_card [Fintype F]
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) :
    Nat.card W.toAffine.Point = Fintype.card F + 1 := by
  rw [← Nat.card_congr (nonsplitNodeChartEquiv W h3 h4 h6), Nat.card_eq_fintype_card,
    Fintype.card_option]

/-- The tangent norm-one subgroup of a normalized node has |F|+1 elements. -/
theorem nodeTangentNormOne_card [Fintype F]
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hb : W.b₂ ≠ 0) :
    Nat.card (nodeTangentNormOne W) = Fintype.card F + 1 := by
  classical
  rw [← Nat.card_congr (Additive.toMul : Additive (nodeTangentNormOne W) ≃ _),
    ← Nat.card_congr (nonsplitNodeNormOneAddEquiv W h3 h4 h6 hb).toEquiv]
  exact nonsplitNodePoint_card W h3 h4 h6

end FLT.Mazur
