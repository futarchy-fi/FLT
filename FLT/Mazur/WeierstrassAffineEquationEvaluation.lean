/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineMonicComparison

/-!
# Evaluation of the affine coordinate ring from an actual equation

A solution over a specified coefficient ring map defines a ring map from
the monic Weierstrass coordinate ring. Its values on both coordinates and
the coefficient polynomial ring are retained explicitly.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassAffineEquationEvaluation
open Polynomial WeierstrassCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S]
  (W : WeierstrassCurve R) (φ : R →+* S) (x y : S)

/-- An affine equation is the vanishing needed to evaluate the monic quadratic. -/
theorem polynomial_eval_zero (he : (W.map φ).toAffine.Equation x y) :
    W.toAffine.polynomial.eval₂ (eval₂RingHom φ x) y = 0 := by
  rw [WeierstrassIntegralChart.affineMonicPolynomial_eval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]
  rw [Affine.equation_iff] at he
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at he
  linear_combination he

/-- Evaluate the actual monic coordinate ring at the two given functions. -/
def evaluation (he : (W.map φ).toAffine.Equation x y) : W.toAffine.CoordinateRing →+* S :=
  AdjoinRoot.lift (eval₂RingHom φ x) y (polynomial_eval_zero W φ x y he)

/-- Evaluation on the polynomial coefficient ring is ordinary substitution in x. -/
theorem evaluation_polynomial (he : (W.map φ).toAffine.Equation x y) (p : R[X]) :
    evaluation W φ x y he (algebraMap R[X] W.toAffine.CoordinateRing p) = p.eval₂ φ x := by
  exact AdjoinRoot.lift_of (polynomial_eval_zero W φ x y he)

/-- Evaluation retains the specified map on the original coefficient ring. -/
theorem evaluation_scalar (he : (W.map φ).toAffine.Equation x y) (a : R) :
    evaluation W φ x y he (algebraMap R W.toAffine.CoordinateRing a) = φ a := by
  change evaluation W φ x y he
    (algebraMap R[X] W.toAffine.CoordinateRing (C a)) = φ a
  rw [evaluation_polynomial, eval₂_C]

/-- The coordinate ring map commutes with the original structural scalar map. -/
theorem evaluation_comp_scalar (he : (W.map φ).toAffine.Equation x y) :
    (evaluation W φ x y he).comp (algebraMap R W.toAffine.CoordinateRing) = φ :=
  RingHom.ext (evaluation_scalar W φ x y he)

/-- The x coordinate is sent to the prescribed original function. -/
theorem evaluation_x (he : (W.map φ).toAffine.Equation x y) :
    evaluation W φ x y he (algebraMap R[X] W.toAffine.CoordinateRing X) = x := by
  rw [evaluation_polynomial, eval₂_X]

/-- The y coordinate is sent to the prescribed original function. -/
theorem evaluation_y (he : (W.map φ).toAffine.Equation x y) :
    evaluation W φ x y he (AdjoinRoot.root W.toAffine.polynomial) = y :=
  AdjoinRoot.lift_root (polynomial_eval_zero W φ x y he)

end FLT.Mazur.WeierstrassAffineEquationEvaluation
