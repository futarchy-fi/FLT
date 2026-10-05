/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedSingularity

/-!
# Transport of singular points through variable changes

A variable change whose new coefficients a₃,a₄,a₆ vanish sends the origin
to a singular point of the original equation. Composing with translation
therefore transports singular-point existence through any variable change.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- A variable change normalizing the singularity identifies its original coordinates. -/
theorem singular_of_variableChange_coefficients (C : VariableChange F)
    (h₃ : (C • W).a₃ = 0) (h₄ : (C • W).a₄ = 0) (h₆ : (C • W).a₆ = 0) :
    W.toAffine.Equation C.r C.t ∧ ¬ W.toAffine.Nonsingular C.r C.t := by
  have hu : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  rw [variableChange_a₃, mul_eq_zero] at h₃
  rw [variableChange_a₄, mul_eq_zero] at h₄
  rw [variableChange_a₆, mul_eq_zero] at h₆
  have h3 := h₃.resolve_left (pow_ne_zero _ hu)
  have h4 := h₄.resolve_left (pow_ne_zero _ hu)
  have h6 := h₆.resolve_left (pow_ne_zero _ hu)
  have he : W.toAffine.Equation C.r C.t := by
    rw [Affine.equation_iff']
    linear_combination -h6
  have hx : W.a₁ * C.t - (3 * C.r ^ 2 + 2 * W.a₂ * C.r + W.a₄) = 0 := by
    linear_combination -h4 - C.s * h3
  have hy : 2 * C.t + W.a₁ * C.r + W.a₃ = 0 := by
    linear_combination h3
  exact ⟨he, by simp [Affine.nonsingular_iff', hx, hy]⟩

/-- Existence of a singular affine point transports back through an admissible change. -/
theorem exists_singular_of_variableChange (C : VariableChange F)
    (h : ∃ x y, (C • W).toAffine.Equation x y ∧
      ¬ (C • W).toAffine.Nonsingular x y) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  obtain ⟨x, y, he, hn⟩ := h
  obtain ⟨h3, h4, h6⟩ := translated_singular_coefficients (C • W) he hn
  rw [← mul_smul] at h3 h4 h6
  exact ⟨_, _, singular_of_variableChange_coefficients W _ h3 h4 h6⟩

/-- Singular-point existence is unchanged by an admissible variable change. -/
theorem exists_singular_variableChange_iff (C : VariableChange F) :
    (∃ x y, (C • W).toAffine.Equation x y ∧ ¬ (C • W).toAffine.Nonsingular x y) ↔
      ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  refine ⟨exists_singular_of_variableChange W C, fun h => ?_⟩
  apply exists_singular_of_variableChange (C • W) C⁻¹
  simpa only [inv_smul_smul] using h

end FLT.Mazur
