/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedSingularity

/-!
# The slope chart on a normalized singular cubic

Smooth affine points have nonzero x and are determined by y/x. These
formulas apply to both split and nonsplit tangents in every characteristic.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
include h3 h4 h6

/-- Smooth affine points on a normalized singular cubic have nonzero x. -/
theorem normalized_nonsingular_x_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y) :
    x ≠ 0 := by
  intro hx
  have he := (Affine.equation_iff' x y).mp h.1
  have hy : y = 0 := by simpa [hx, h3, h6] using he
  exact (normalized_nonsingular_iff W h3 h4 h6 h.1).mp h ⟨hx, hy⟩

/-- Recover both affine coordinates from the slope of the line through the singularity. -/
theorem normalized_coordinates_slope {x y : F} (h : W.toAffine.Nonsingular x y) :
    (y / x) ^ 2 + W.a₁ * (y / x) - W.a₂ = x ∧
      (y / x) * ((y / x) ^ 2 + W.a₁ * (y / x) - W.a₂) = y := by
  have hx := normalized_nonsingular_x_ne_zero W h3 h4 h6 h
  have he := (Affine.equation_iff' x y).mp h.1
  simp only [h3, h4, h6, zero_mul, add_zero] at he
  have ex : (y / x) ^ 2 + W.a₁ * (y / x) - W.a₂ = x := by
    field_simp
    linear_combination he
  exact ⟨ex, by rw [ex]; exact div_mul_cancel₀ y hx⟩

end FLT.Mazur
