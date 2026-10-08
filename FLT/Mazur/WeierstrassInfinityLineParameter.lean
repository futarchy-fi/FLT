/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineReconstruction

/-!
# An invertible parameter change at a normalized third intersection

The output line supplies a determinant-one change of its two parameters.
It sends the homogeneous third factor to U. After point negation the resulting
Y coordinate is V, even when the old third point's Y coordinate is not a unit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Negation preserves the value of the cubic, including away from its zero locus. -/
theorem infinityCubic_negate (X Y Z : R) :
    eval ![X, -Y - W.a₁ * X - W.a₃ * Z, Z] W.toProjective.polynomial =
      eval ![X, Y, Z] W.toProjective.polynomial := by
  simp only [Projective.eval_polynomial, Projective.fin3_def_ext]
  ring

/-- The line relation supplies the determinant-one identity for the parameter change. -/
theorem infinity_negated_line_determinant {u v m b : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) :
    -(1 + W.a₃ * b) * (-1 - W.a₁ * u - W.a₃ * v) -
      u * (W.a₁ + W.a₃ * m) = 1 := by
  linear_combination W.a₃ * h

/-- The third factor becomes exactly the first new parameter. -/
theorem infinity_negated_line_parameter_third {u v m b : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) (U V : R) :
    let n := -1 - W.a₁ * u - W.a₃ * v
    n * (-(1 + W.a₃ * b) * U + u * V) -
      u * ((W.a₁ + W.a₃ * m) * U + n * V) = U := by
  dsimp only
  linear_combination U * infinity_negated_line_determinant W h

/-- The second row of the inverse parameter change is explicit as well. -/
theorem infinity_negated_line_parameter_inverse {u v m b : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) (U V : R) :
    let n := -1 - W.a₁ * u - W.a₃ * v
    (-(W.a₁ + W.a₃ * m)) * (-(1 + W.a₃ * b) * U + u * V) -
      (1 + W.a₃ * b) * ((W.a₁ + W.a₃ * m) * U + n * V) = V := by
  dsimp only
  linear_combination V * infinity_negated_line_determinant W h

/-- The transformed line has normalized Y coordinate V after negation. -/
theorem infinity_negated_line_parameter_cubic {u v m b : R}
    (h : v - m * u - b * (-1 - W.a₁ * u - W.a₃ * v) = 0) (U V : R) :
    let n := -1 - W.a₁ * u - W.a₃ * v
    let X := -(1 + W.a₃ * b) * U + u * V
    let Y := (W.a₁ + W.a₃ * m) * U + n * V
    eval ![X, V, (W.a₁ * b - m) * U + v * V] W.toProjective.polynomial =
      eval ![X, Y, m * X + b * Y] W.toProjective.polynomial := by
  dsimp only
  have hz : m * (-(1 + W.a₃ * b) * U + u * V) +
      b * ((W.a₁ + W.a₃ * m) * U + (-1 - W.a₁ * u - W.a₃ * v) * V) =
        (W.a₁ * b - m) * U + v * V := by
    linear_combination -V * h
  rw [hz]
  have hy : (W.a₁ + W.a₃ * m) * U + (-1 - W.a₁ * u - W.a₃ * v) * V =
      -V - W.a₁ * (-(1 + W.a₃ * b) * U + u * V) -
        W.a₃ * ((W.a₁ * b - m) * U + v * V) := by ring
  rw [hy, infinityCubic_negate]

end FLT.Mazur.WeierstrassIntegralChart
