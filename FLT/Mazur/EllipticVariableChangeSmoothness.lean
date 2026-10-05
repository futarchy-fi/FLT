/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Variable changes preserve smoothness of singular and smooth cubics

The triangular change of the two partial derivatives proves preservation of
nonsingularity without an ellipticity assumption. This applies to bad special
fibers as well as the generic elliptic curve.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-- The y partial derivative scales by u³. -/
theorem variableChange_partialY (x y : F) :
    2 * ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) +
        W.a₁ * ((C.u : F) ^ 2 * x + C.r) + W.a₃ =
      (C.u : F) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  simp [variableChange_a₁, variableChange_a₃]
  field

/-- The x partial derivative transforms triangularly with the y partial derivative. -/
theorem variableChange_partialX (x y : F) :
    W.a₁ * ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) -
        (3 * ((C.u : F) ^ 2 * x + C.r) ^ 2 +
          2 * W.a₂ * ((C.u : F) ^ 2 * x + C.r) + W.a₄) =
      (C.u : F) ^ 4 * ((C • W).a₁ * y -
        (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄)) -
      C.s * (C.u : F) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
  field

/-- Admissible variable changes preserve nonsingularity even when the cubic is singular. -/
theorem variableChange_nonsingular (x y : F) :
    W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) ↔
      (C • W).toAffine.Nonsingular x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [Affine.nonsingular_iff', Affine.nonsingular_iff',
    Affine.variableChange_equation, variableChange_partialX, variableChange_partialY]
  constructor
  · rintro ⟨he, hd⟩
    refine ⟨he, ?_⟩
    by_contra hn
    push Not at hn
    simp only [hn.1, hn.2, mul_zero, sub_zero, ne_self_iff_false, or_self] at hd
  · rintro ⟨he, hd⟩
    refine ⟨he, ?_⟩
    by_contra hn
    push Not at hn
    have hy := (mul_eq_zero.mp hn.2).resolve_left (pow_ne_zero 3 hu)
    have hx := hn.1
    simp only [hy, mul_zero, sub_zero, mul_eq_zero, pow_ne_zero 4 hu, false_or] at hx
    exact hd.elim (fun h => h hx) (fun h => h hy)

end FLT.Mazur
