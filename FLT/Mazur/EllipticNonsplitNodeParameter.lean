/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentFieldFixed
public import FLT.Mazur.EllipticNormalizedSlope
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The norm-one parameter of a nonsplit node

On a normalized nonsplit node, the ratio of the two tangent factors is
nonzero and conjugation sends it to its inverse. The parameter distinguishes
all actual smooth points. Surjectivity and the group law are separate steps.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]

local notation "L" => AdjoinRoot (nodeTangentPolynomial W)

/-- The two tangent factors multiply to x³ on a normalized nodal cubic. -/
theorem nodeTangentPoint_factorization (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    {x y : F} (h : W.toAffine.Equation x y) :
    (algebraMap F L y - AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap F L x) *
      (algebraMap F L y + (algebraMap F L W.a₁ + AdjoinRoot.root (nodeTangentPolynomial W)) *
        algebraMap F L x) = algebraMap F L x ^ 3 := by
  have he := (Affine.equation_iff' x y).mp h
  simp only [h3, h4, h6, zero_mul, add_zero] at he
  have hm := congrArg (algebraMap F L) he
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hm
  linear_combination hm - (algebraMap F L x) ^ 2 * nodeTangentRoot_equation W

/-- Both tangent factors are nonzero at a smooth point. -/
theorem nodeTangentPoint_factors_ne_zero
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    algebraMap F L y - AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap F L x ≠ 0 ∧
      algebraMap F L y + (algebraMap F L W.a₁ + AdjoinRoot.root (nodeTangentPolynomial W)) *
        algebraMap F L x ≠ 0 := by
  apply mul_ne_zero_iff.mp
  rw [nodeTangentPoint_factorization W h3 h4 h6 h.1]
  exact pow_ne_zero 3 ((map_ne_zero_iff _ (algebraMap F L).injective).mpr
    (normalized_nonsingular_x_ne_zero W h3 h4 h6 h))

/-- The ratio of tangent factors, with value one at infinity. -/
noncomputable def nodeTangentPointParameter : W.toAffine.Point → L
  | .zero => 1
  | .some x y _ =>
    (algebraMap F L y - AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap F L x) /
      (algebraMap F L y + (algebraMap F L W.a₁ + AdjoinRoot.root (nodeTangentPolynomial W)) *
        algebraMap F L x)

/-- The tangent ratio is a unit at every smooth point. -/
theorem nodeTangentPointParameter_ne_zero
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (P : W.toAffine.Point) :
    nodeTangentPointParameter W P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h =>
    exact div_ne_zero (nodeTangentPoint_factors_ne_zero W h3 h4 h6 h).1
      (nodeTangentPoint_factors_ne_zero W h3 h4 h6 h).2

/-- The tangent parameter has conjugation norm one. -/
theorem nodeTangentPointParameter_norm_one
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (P : W.toAffine.Point) :
    nodeTangentConjugation W (nodeTangentPointParameter W P) *
      nodeTangentPointParameter W P = 1 := by
  cases P with
  | zero => simp [nodeTangentPointParameter]
  | some x y h =>
    obtain ⟨hn, hd⟩ := nodeTangentPoint_factors_ne_zero W h3 h4 h6 h
    have hr : nodeTangentConjugation W (AdjoinRoot.root (nodeTangentPolynomial W)) =
        -algebraMap F L W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) :=
      nodeTangentConjugationHom_root W
    simp only [nodeTangentPointParameter, map_div₀, map_add, map_sub, map_mul,
      AlgEquiv.commutes, hr]
    have hn' : algebraMap F L y - (-algebraMap F L W.a₁ -
        AdjoinRoot.root (nodeTangentPolynomial W)) * algebraMap F L x =
        algebraMap F L y + (algebraMap F L W.a₁ + AdjoinRoot.root (nodeTangentPolynomial W)) *
          algebraMap F L x := by ring
    have hd' : algebraMap F L y + (algebraMap F L W.a₁ + (-algebraMap F L W.a₁ -
        AdjoinRoot.root (nodeTangentPolynomial W))) * algebraMap F L x =
        algebraMap F L y - AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap F L x := by ring
    rw [hn', hd']
    field_simp

/-- Only infinity has tangent ratio one, when the node is separable. -/
theorem nodeTangentPointParameter_eq_one_iff
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hb : W.b₂ ≠ 0)
    (P : W.toAffine.Point) : nodeTangentPointParameter W P = 1 ↔ P = 0 := by
  cases P with
  | zero => simp [nodeTangentPointParameter, Affine.Point.zero_def]
  | some x y h =>
    have hd := (nodeTangentPoint_factors_ne_zero W h3 h4 h6 h).2
    have hu := (nodeTangentRoot_derivative_isUnit W (isUnit_iff_ne_zero.mpr hb)).ne_zero
    have hx : algebraMap F L x ≠ 0 := (map_ne_zero_iff _ (algebraMap F L).injective).mpr
      (normalized_nonsingular_x_ne_zero W h3 h4 h6 h)
    have hn : nodeTangentPointParameter W (.some x y h) ≠ 1 := by
      intro he
      have he' := (div_eq_one_iff_eq hd).mp he
      apply mul_ne_zero hu hx
      linear_combination -he'
    simp only [hn, Affine.Point.zero_def, reduceCtorEq]

/-- The tangent ratio distinguishes all smooth points of a normalized nonsplit node. -/
theorem nodeTangentPointParameter_injective
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hb : W.b₂ ≠ 0) :
    Function.Injective (nodeTangentPointParameter W) := by
  intro P Q he
  cases P with
  | zero => exact ((nodeTangentPointParameter_eq_one_iff W h3 h4 h6 hb Q).mp he.symm).symm
  | some x y h =>
    cases Q with
    | zero => exact (nodeTangentPointParameter_eq_one_iff W h3 h4 h6 hb _).mp he
    | some x' y' h' =>
      have hd := (nodeTangentPoint_factors_ne_zero W h3 h4 h6 h).2
      have hd' := (nodeTangentPoint_factors_ne_zero W h3 h4 h6 h').2
      have he' := (div_eq_div_iff hd hd').mp he
      have hu := (nodeTangentRoot_derivative_isUnit W (isUnit_iff_ne_zero.mpr hb)).ne_zero
      have hc : algebraMap F L y * algebraMap F L x' -
          algebraMap F L y' * algebraMap F L x = 0 := by
        apply (mul_eq_zero.mp (show (algebraMap F L W.a₁ +
            2 * AdjoinRoot.root (nodeTangentPolynomial W)) *
            (algebraMap F L y * algebraMap F L x' -
              algebraMap F L y' * algebraMap F L x) = 0 by
          linear_combination he')).resolve_left hu
      have hc' : y * x' = y' * x := by
        apply sub_eq_zero.mp
        apply (algebraMap F L).injective
        simpa only [map_sub, map_mul, map_zero] using hc
      have hrs := (div_eq_div_iff (normalized_nonsingular_x_ne_zero W h3 h4 h6 h)
        (normalized_nonsingular_x_ne_zero W h3 h4 h6 h')).mpr hc'
      obtain ⟨ex, ey⟩ := normalized_coordinates_slope W h3 h4 h6 h
      obtain ⟨ex', ey'⟩ := normalized_coordinates_slope W h3 h4 h6 h'
      apply (Affine.Point.some.injEq _ _ _ _ _ _).mpr
      exact ⟨by rw [← ex, ← ex', hrs], by rw [← ey, ← ey', hrs]⟩

end FLT.Mazur
