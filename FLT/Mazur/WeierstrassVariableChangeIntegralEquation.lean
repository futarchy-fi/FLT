/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeScaledCoefficients
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Admissible coordinate changes preserve the integral affine equation

The original polynomial is the transformed polynomial times the sixth power
of the scale. Cancelling this unit proves equation transport over all rings,
including rings with nilpotents and in characteristic three.
-/

@[expose] public section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassVariableChangeIntegralEquation

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The actual integral affine polynomial scales with weight six. -/
theorem polynomial (x y : R) :
    W.toAffine.polynomial.evalEval ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t) =
      (C.u : R) ^ 6 * (C • W).toAffine.polynomial.evalEval x y := by
  simp only [Affine.evalEval_polynomial]
  linear_combination
    -(C.u : R) ^ 5 * x * y * WeierstrassVariableChangeScaledCoefficients.a₁ W C +
      (C.u : R) ^ 4 * x ^ 2 * WeierstrassVariableChangeScaledCoefficients.a₂ W C -
      (C.u : R) ^ 3 * y * WeierstrassVariableChangeScaledCoefficients.a₃ W C +
      (C.u : R) ^ 2 * x * WeierstrassVariableChangeScaledCoefficients.a₄ W C +
      WeierstrassVariableChangeScaledCoefficients.a₆ W C

/-- An admissible change preserves the equation without any field hypothesis. -/
theorem equation_iff (x y : R) :
    W.toAffine.Equation ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t) ↔
      (C • W).toAffine.Equation x y := by
  change _ = 0 ↔ _ = 0
  rw [polynomial]
  exact (C.u.isUnit.pow 6).mul_right_eq_zero

end FLT.Mazur.WeierstrassVariableChangeIntegralEquation
