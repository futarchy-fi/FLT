/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRationalSingularity

/-!
# The repeated tangent of a normalized cuspidal cubic

For a singularity at the origin, c₄ is the square of b₂. Its vanishing
makes the quadratic tangent cone a square over a perfect field, including
characteristic two. A shear then removes a₁ and a₂ as well as a₃,a₄,a₆.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- At a normalized singularity, c₄ is the square of the tangent discriminant b₂. -/
theorem normalized_c₄_eq_b₂_sq (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) :
    W.c₄ = W.b₂ ^ 2 := by
  simp [c₄, b₄, h3, h4]

/-- The normalized equation is its quadratic tangent cone minus the cubic x³. -/
theorem normalized_equation_tangent (h3 : W.a₃ = 0) (h4 : W.a₄ = 0)
    (h6 : W.a₆ = 0) (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 + W.a₁ * x * y - W.a₂ * x ^ 2 = x ^ 3 := by
  rw [Affine.equation_iff]
  simp only [toAffine, h3, h4, h6, zero_mul, add_zero]
  constructor <;> intro h <;> linear_combination h

/-- A zero tangent discriminant has a rational repeated tangent over a perfect field. -/
theorem exists_cusp_shear [PerfectField F] (hb : W.b₂ = 0) :
    ∃ s : F, W.a₁ + 2 * s = 0 ∧ W.a₂ - s * W.a₁ - s ^ 2 = 0 := by
  rw [b₂] at hb
  by_cases h2 : (2 : F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero (by decide)).mpr h2
    have h1 : W.a₁ = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 2)
      linear_combination hb - 2 * W.a₂ * h2
    obtain ⟨s, hs⟩ := surjective_frobenius F 2 W.a₂
    change s ^ 2 = W.a₂ at hs
    exact ⟨s, by simp [h1, h2], by simp [h1, hs]⟩
  · refine ⟨-W.a₁ / 2, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      linear_combination hb

/-- The repeated tangent factors the tangent cone as one squared linear form. -/
theorem cusp_tangent_square {s : F} (h1 : W.a₁ + 2 * s = 0)
    (h2 : W.a₂ - s * W.a₁ - s ^ 2 = 0) (x y : F) :
    y ^ 2 + W.a₁ * x * y - W.a₂ * x ^ 2 = (y - s * x) ^ 2 := by
  linear_combination (x * y - s * x ^ 2) * h1 - x ^ 2 * h2

/-- A normalized cusp can be sheared to y²=x³ over any perfect field. -/
theorem exists_normalized_cusp_shear [PerfectField F]
    (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0) (hc : W.c₄ = 0) :
    ∃ s : F, let V := VariableChange.mk 1 0 s 0 • W
      V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0 ∧ V.a₄ = 0 ∧ V.a₆ = 0 := by
  have hb : W.b₂ = 0 := by
    rw [normalized_c₄_eq_b₂_sq W h3 h4] at hc
    exact eq_zero_of_pow_eq_zero hc
  obtain ⟨s, hs1, hs2⟩ := exists_cusp_shear W hb
  refine ⟨s, ?_⟩
  simpa [variableChange_def, h3, h4, h6] using And.intro hs1 hs2

end FLT.Mazur
