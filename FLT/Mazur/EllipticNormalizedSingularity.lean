/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Singular points of a normalized Weierstrass cubic

When a₃=a₄=a₆=0, the origin is the unique singular affine point.
The proof uses the equation and its two partial derivatives and is valid in
every characteristic. Translating a given singular point to the origin gives
exactly these coefficient conditions. Existence of a rational singular point
from vanishing discriminant over a perfect field is a separate obligation.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- A normalized Weierstrass cubic has only the origin as a singular affine point. -/
theorem eq_zero_of_normalized_singular (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
    {x y : F} (he : W.toAffine.Equation x y) (hn : ¬ W.toAffine.Nonsingular x y) :
    x = 0 ∧ y = 0 := by
  have he' := (Affine.equation_iff' x y).mp he
  have hd : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧
      2 * y + W.a₁ * x + W.a₃ = 0 := by
    simpa only [Affine.nonsingular_iff', he, true_and, not_or, not_not] using hn
  obtain ⟨hdx, hdy⟩ := hd
  simp only [h₃, h₄, h₆, zero_mul, add_zero] at he' hdx hdy
  have hx3 : x ^ 3 = 0 := by
    linear_combination 2 * he' - x * hdx - y * hdy
  have hx : x = 0 := eq_zero_of_pow_eq_zero hx3
  have hy2 : y ^ 2 = 0 := by simpa [hx] using he'
  exact ⟨hx, eq_zero_of_pow_eq_zero hy2⟩

/-- On a normalized cubic, all affine points except the origin are nonsingular. -/
theorem normalized_nonsingular_iff (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
    {x y : F} (he : W.toAffine.Equation x y) :
    W.toAffine.Nonsingular x y ↔ ¬ (x = 0 ∧ y = 0) := by
  constructor
  · rintro hn ⟨rfl, rfl⟩
    simp only [Affine.nonsingular_zero, h₃, h₄, ne_self_iff_false, or_self, and_false] at hn
  · intro h
    by_contra hn
    exact h (eq_zero_of_normalized_singular W h₃ h₄ h₆ he hn)

/-- Translating any singular point to the origin kills a₃,a₄,a₆. -/
theorem translated_singular_coefficients {x y : F} (he : W.toAffine.Equation x y)
    (hn : ¬ W.toAffine.Nonsingular x y) :
    let V := VariableChange.mk 1 x 0 y • W
    V.a₃ = 0 ∧ V.a₄ = 0 ∧ V.a₆ = 0 := by
  have he0 := (Affine.equation_iff_variableChange x y).mp he
  have hn0 : ¬ (VariableChange.mk 1 x 0 y • W).toAffine.Nonsingular 0 0 :=
    fun h => hn ((Affine.nonsingular_iff_variableChange x y).mpr h)
  have h₆ := Affine.equation_zero.mp he0
  have h34 : (VariableChange.mk 1 x 0 y • W).a₃ = 0 ∧
      (VariableChange.mk 1 x 0 y • W).a₄ = 0 := by
    simpa only [Affine.nonsingular_zero, h₆, true_and, not_or, not_not] using hn0
  exact ⟨h34.1, h34.2, h₆⟩

end FLT.Mazur
