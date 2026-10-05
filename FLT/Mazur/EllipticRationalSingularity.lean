/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSingularSmallChar

/-!
# Rational singular points over perfect fields

A Weierstrass equation with zero discriminant over a perfect field has a
rational singular point. The proof includes characteristics two and three.
Away from those characteristics, a short equation gives the singular point
by a rational formula, so that branch does not require perfectness.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The explicit singular point of a short equation away from characteristics two and three. -/
theorem exists_singular_short_of_two_three_ne_zero [W.IsShortNF]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hΔ : W.Δ = 0) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  have h16 : (16 : F) ≠ 0 := by
    convert pow_ne_zero 4 h2 using 1
    norm_num
  have hd : 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 = 0 := by
    rw [W.Δ_of_isShortNF, mul_eq_zero] at hΔ
    exact hΔ.resolve_left (neg_ne_zero.mpr h16)
  by_cases h4 : W.a₄ = 0
  · have h27 : (27 : F) ≠ 0 := by
      convert pow_ne_zero 3 h3 using 1
      norm_num
    have h6 : W.a₆ = 0 := by
      simpa only [h4, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_add,
        mul_eq_zero, h27, false_or, pow_eq_zero_iff (by decide : 2 ≠ 0)] using hd
    exact ⟨0, 0, by simpa using h6, by simp [Affine.nonsingular_zero, h4]⟩
  · let x := -3 * W.a₆ / (2 * W.a₄)
    have hx : 3 * x ^ 2 + W.a₄ = 0 := by
      dsimp [x]
      field_simp [h2, h4]
      linear_combination hd
    have he : x ^ 3 + W.a₄ * x + W.a₆ = 0 := by
      dsimp [x]
      field_simp [h2, h4]
      linear_combination -W.a₆ * hd
    refine ⟨x, 0, ?_, ?_⟩
    · simpa [Affine.equation_iff] using he.symm
    · simp [Affine.nonsingular_iff', hx]

/-- Zero discriminant over any perfect field yields a rational singular affine point. -/
theorem exists_singular_of_discriminant_zero [PerfectField F] (hΔ : W.Δ = 0) :
    ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  by_cases h2 : (2 : F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero (by decide)).mpr h2
    exact exists_singular_char_two W hΔ
  by_cases h3 : (3 : F) = 0
  · let : CharP F 3 := (CharP.charP_iff_prime_eq_zero (by decide)).mpr h3
    exact exists_singular_char_three W hΔ
  let : Invertible (2 : F) := invertibleOfNonzero h2
  let : Invertible (3 : F) := invertibleOfNonzero h3
  obtain ⟨C, hC⟩ := W.exists_variableChange_isShortNF
  let := hC
  apply exists_singular_of_variableChange W C
  apply exists_singular_short_of_two_three_ne_zero _ h2 h3
  rw [variableChange_Δ, hΔ, mul_zero]

/-- Over a perfect field, discriminant zero is equivalent to a rational singularity. -/
theorem discriminant_zero_iff_exists_singular [PerfectField F] :
    W.Δ = 0 ↔ ∃ x y, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  refine ⟨exists_singular_of_discriminant_zero W, ?_⟩
  rintro ⟨x, y, he, hn⟩
  by_contra hΔ
  exact hn ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp he)

end FLT.Mazur
