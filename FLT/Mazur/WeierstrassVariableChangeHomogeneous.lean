/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeScaledCoefficients
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Integral homogeneous coordinate transport

An admissible change acts on all three homogeneous coordinates, including
points at infinity. Its cubic identity is valid over every commutative ring.
-/

@[expose] public noncomputable section

open WeierstrassCurve MvPolynomial

namespace FLT.Mazur.WeierstrassVariableChangeHomogeneous

variable {R : Type*} [CommRing R] (C D : VariableChange R)

/-- Homogeneous coordinates before the admissible change. -/
def coordinates (P : Fin 3 → R) : Fin 3 → R :=
  ![(C.u : R) ^ 2 * P 0 + C.r * P 2,
    (C.u : R) ^ 3 * P 1 + (C.u : R) ^ 2 * C.s * P 0 + C.t * P 2, P 2]

/-- Composition uses the same order as the Weierstrass variable-change action. -/
theorem coordinates_mul (P : Fin 3 → R) :
    coordinates (C * D) P = coordinates D (coordinates C P) := by
  ext i
  fin_cases i <;> simp [coordinates, VariableChange.mul_def] <;> ring

/-- The identity change fixes the entire coordinate vector. -/
@[simp] theorem coordinates_one (P : Fin 3 → R) : coordinates 1 P = P := by
  ext i
  fin_cases i <;> simp [coordinates, VariableChange.one_def]

/-- The inverse change recovers every vector, without a nonvanishing hypothesis. -/
@[simp] theorem coordinates_inv (P : Fin 3 → R) :
    coordinates C⁻¹ (coordinates C P) = P := by
  rw [← coordinates_mul, mul_inv_cancel, coordinates_one]

/-- The homogeneous cubic scales by the sixth power of the unit. -/
theorem eval_polynomial (W : WeierstrassCurve R) (P : Fin 3 → R) :
    eval (coordinates C P) W.toProjective.polynomial =
      (C.u : R) ^ 6 * eval P (C • W).toProjective.polynomial := by
  simp only [Projective.eval_polynomial, coordinates, Projective.fin3_def_ext]
  linear_combination
    -(C.u : R) ^ 5 * P 0 * P 1 * P 2 *
      WeierstrassVariableChangeScaledCoefficients.a₁ W C +
    (C.u : R) ^ 4 * P 0 ^ 2 * P 2 *
      WeierstrassVariableChangeScaledCoefficients.a₂ W C -
    (C.u : R) ^ 3 * P 1 * P 2 ^ 2 *
      WeierstrassVariableChangeScaledCoefficients.a₃ W C +
    (C.u : R) ^ 2 * P 0 * P 2 ^ 2 *
      WeierstrassVariableChangeScaledCoefficients.a₄ W C +
    P 2 ^ 3 * WeierstrassVariableChangeScaledCoefficients.a₆ W C

/-- Both directions of equation transport hold even over nonreduced bases. -/
theorem equation_iff (W : WeierstrassCurve R) (P : Fin 3 → R) :
    W.toProjective.Equation (coordinates C P) ↔ (C • W).toProjective.Equation P := by
  change _ = 0 ↔ _ = 0
  rw [eval_polynomial]
  exact (C.u.isUnit.pow 6).mul_right_eq_zero

end FLT.Mazur.WeierstrassVariableChangeHomogeneous
