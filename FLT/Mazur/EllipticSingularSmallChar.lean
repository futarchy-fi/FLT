/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSingularVariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.FieldTheory.Perfect

/-!
# Rational singular points in characteristics two and three

Vanishing discriminant gives a rational singular point in the standard
normal forms. Perfectness supplies the square or cube roots needed for
cuspidal equations; the nodal cases have a singular point at the origin.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] [PerfectField F] (W : WeierstrassCurve F)

/-- A singular short equation in characteristic three has a rational cusp. -/
theorem exists_singular_short_char_three [CharP F 3] [W.IsShortNF] (hΔ : W.Δ = 0) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  have hthree : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h4 : W.a₄ = 0 := by
    rw [W.Δ_of_isShortNF_of_char_three, neg_eq_zero] at hΔ
    exact eq_zero_of_pow_eq_zero hΔ
  obtain ⟨x, hx⟩ := surjective_frobenius F 3 (-W.a₆)
  change x ^ 3 = -W.a₆ at hx
  refine ⟨x, 0, ?_, ?_⟩
  · simp [Affine.equation_iff', h4, hx]
  · simp [Affine.nonsingular_iff', h4, hthree]

/-- A characteristic-three normal form with zero discriminant has a rational singular point. -/
theorem exists_singular_normal_char_three [CharP F 3] [W.IsCharThreeNF]
    (hΔ : W.Δ = 0) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  cases ‹W.IsCharThreeNF› with
  | of_j_eq_zero => exact exists_singular_short_char_three W hΔ
  | of_j_ne_zero =>
    by_cases h2 : W.a₂ = 0
    · let : W.IsShortNF := ⟨by simp, h2, by simp⟩
      exact exists_singular_short_char_three W hΔ
    · have h6 : W.a₆ = 0 := by
        rw [W.Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_eq_zero] at hΔ
        exact hΔ.resolve_left (neg_ne_zero.mpr (pow_ne_zero _ h2))
      exact ⟨0, 0, by simpa using h6, by simp [Affine.nonsingular_zero]⟩

/-- A characteristic-two normal form with zero discriminant has a rational singular point. -/
theorem exists_singular_normal_char_two [CharP F 2] [W.IsCharTwoNF]
    (hΔ : W.Δ = 0) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  cases ‹W.IsCharTwoNF› with
  | of_j_ne_zero =>
    have h6 : W.a₆ = 0 := by simpa using hΔ
    exact ⟨0, 0, by simpa using h6, by simp [Affine.nonsingular_zero]⟩
  | of_j_eq_zero =>
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h3 : W.a₃ = 0 := by
      rw [W.Δ_of_isCharTwoJEqZeroNF_of_char_two] at hΔ
      exact eq_zero_of_pow_eq_zero hΔ
    obtain ⟨x, hx⟩ := surjective_frobenius F 2 (-W.a₄)
    obtain ⟨y, hy⟩ := surjective_frobenius F 2 (x ^ 3 + W.a₄ * x + W.a₆)
    change x ^ 2 = -W.a₄ at hx
    change y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ at hy
    have hd : 3 * x ^ 2 + W.a₄ = 0 := by
      linear_combination hx + x ^ 2 * CharP.cast_eq_zero F 2
    refine ⟨x, y, ?_, ?_⟩
    · simp [Affine.equation_iff', h3, hy]
    · simp [Affine.nonsingular_iff', h3, hd, htwo]

/-- Every discriminant-zero equation over a perfect field of characteristic two is singular. -/
theorem exists_singular_char_two [CharP F 2] (hΔ : W.Δ = 0) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  obtain ⟨C, hC⟩ := W.exists_variableChange_isCharTwoNF
  let := hC
  apply exists_singular_of_variableChange W C
  apply exists_singular_normal_char_two
  rw [variableChange_Δ, hΔ, mul_zero]

/-- Every discriminant-zero equation over a perfect field of characteristic three is singular. -/
theorem exists_singular_char_three [CharP F 3] (hΔ : W.Δ = 0) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  obtain ⟨C, hC⟩ := W.exists_variableChange_isCharThreeNF
  let := hC
  apply exists_singular_of_variableChange W C
  apply exists_singular_normal_char_three
  rw [variableChange_Δ, hΔ, mul_zero]

end FLT.Mazur
