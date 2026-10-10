/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Scaled coefficients of an admissible change over an arbitrary ring

Multiplying each transformed coefficient by the appropriate unit power
removes all inverse factors. These identities allow integral equation
transport without field division or any restriction on the characteristic.
-/

@[expose] public section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassVariableChangeScaledCoefficients

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The coefficient of XY has weight one. -/
theorem a₁ : (C.u : R) * (C • W).a₁ = W.a₁ + 2 * C.s := by
  rw [variableChange_a₁, ← mul_assoc, C.u.mul_inv, one_mul]

/-- The coefficient of X squared has weight two. -/
theorem a₂ : (C.u : R) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
  rw [variableChange_a₂, ← mul_assoc, ← mul_pow, C.u.mul_inv, one_pow, one_mul]

/-- The coefficient of Y has weight three. -/
theorem a₃ : (C.u : R) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
  rw [variableChange_a₃, ← mul_assoc, ← mul_pow, C.u.mul_inv, one_pow, one_mul]

/-- The coefficient of X has weight four. -/
theorem a₄ : (C.u : R) ^ 4 * (C • W).a₄ =
    W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ +
      3 * C.r ^ 2 - 2 * C.s * C.t := by
  rw [variableChange_a₄, ← mul_assoc, ← mul_pow, C.u.mul_inv, one_pow, one_mul]

/-- The constant coefficient has weight six. -/
theorem a₆ : (C.u : R) ^ 6 * (C • W).a₆ =
    W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 -
      C.r * C.t * W.a₁ := by
  rw [variableChange_a₆, ← mul_assoc, ← mul_pow, C.u.mul_inv, one_pow, one_mul]

end FLT.Mazur.WeierstrassVariableChangeScaledCoefficients
