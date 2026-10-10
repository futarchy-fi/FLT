/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeScaledCoefficients
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Integral addition formulas under admissible coordinate changes

The slope transforms by u*l+s. Both output coordinates commute with the
original affine change over arbitrary rings, including nonreduced rings.
-/

@[expose] public section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassVariableChangeAdditionFormula

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The transformed line satisfies the original secant relation. -/
theorem line_relation (x₁ x₂ y₁ y₂ l : R) (hl : l * (x₁ - x₂) = y₁ - y₂) :
    ((C.u : R) * l + C.s) *
        (((C.u : R) ^ 2 * x₁ + C.r) - ((C.u : R) ^ 2 * x₂ + C.r)) =
      ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t) -
        ((C.u : R) ^ 3 * y₂ + (C.u : R) ^ 2 * C.s * x₂ + C.t) := by
  linear_combination (C.u : R) ^ 3 * hl

/-- Addition's X coordinate commutes with the integral admissible change. -/
theorem addX (x₁ x₂ l : R) :
    W.toAffine.addX ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) * l + C.s) =
      (C.u : R) ^ 2 * (C • W).toAffine.addX x₁ x₂ l + C.r := by
  simp only [Affine.addX]
  linear_combination -((C.u : R) * l) *
    WeierstrassVariableChangeScaledCoefficients.a₁ W C +
    WeierstrassVariableChangeScaledCoefficients.a₂ W C

/-- Addition's Y coordinate commutes with the same integral admissible change. -/
theorem addY (x₁ x₂ y₁ l : R) :
    W.toAffine.addY ((C.u : R) ^ 2 * x₁ + C.r) ((C.u : R) ^ 2 * x₂ + C.r)
        ((C.u : R) ^ 3 * y₁ + (C.u : R) ^ 2 * C.s * x₁ + C.t)
        ((C.u : R) * l + C.s) =
      (C.u : R) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ l +
        (C.u : R) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ l + C.t := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY]
  rw [addX]
  linear_combination
    ((C.u : R) ^ 2 * (C • W).toAffine.addX x₁ x₂ l) *
      WeierstrassVariableChangeScaledCoefficients.a₁ W C +
      WeierstrassVariableChangeScaledCoefficients.a₃ W C

end FLT.Mazur.WeierstrassVariableChangeAdditionFormula
