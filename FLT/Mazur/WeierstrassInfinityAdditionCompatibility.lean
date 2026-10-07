/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# Comparing the infinity addition formula with the projective secant law

The old projective polynomials equal the new infinity formula times the cube
of the difference of input X coordinates. This is an integral polynomial
identity; on a common domain where that difference is a unit it identifies
the represented projective points.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Polarization is linear in the direction, with its diagonal value three times the cubic. -/
theorem cubicPolar_line_right (P D : Fin 3 → R) (d : R) :
    cubicPolar W P (P + d • D) =
      3 * eval P W.toProjective.polynomial + d * cubicPolar W P D := by
  simp only [cubicPolar, Projective.eval_polynomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The other polarization coefficient is quadratic along the same line. -/
theorem cubicPolar_line_left (P D : Fin 3 → R) (d : R) :
    cubicPolar W (P + d • D) P = 3 * eval P W.toProjective.polynomial +
      2 * d * cubicPolar W P D + d ^ 2 * cubicPolar W D P := by
  simp only [cubicPolar, Projective.eval_polynomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Vieta's formula differs from the secant third-intersection polynomial by d cubed. -/
theorem lineThird_compatibility {P D : Fin 3 → R} {d : R}
    (hP : W.toProjective.Equation P)
    (hd : cubicPolar W P D + cubicPolar W D P * d +
      eval D W.toProjective.polynomial * d ^ 2 = 0) :
    thirdIntersection W P (P + d • D) = d ^ 3 • lineThird W P D d := by
  change eval P W.toProjective.polynomial = 0 at hP
  ext i
  simp only [thirdIntersection, cubicPolar_line_right, cubicPolar_line_left, hP,
    lineThird, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination d * (d * D i - P i) * hd

/-- Mathlib's polynomial addition is elliptic negation of the secant third intersection. -/
theorem projectiveAdd_eq_negThird (P Q : Fin 3 → R) :
    W.toProjective.addXYZ P Q = ![thirdIntersection W P Q 0,
      W.toProjective.negY (thirdIntersection W P Q), thirdIntersection W P Q 2] := by
  simp only [Projective.addXYZ, Projective.addY, Projective.negY, thirdIntersection_x,
    thirdIntersection_y, thirdIntersection_z, Projective.fin3_def_ext]

/-- Negation preserves the cubed scale in the comparison of the two addition formulas. -/
theorem projectiveAdd_on_line {P D : Fin 3 → R} {d : R}
    (hP : W.toProjective.Equation P)
    (hd : cubicPolar W P D + cubicPolar W D P * d +
      eval D W.toProjective.polynomial * d ^ 2 = 0) :
    W.toProjective.addXYZ P (P + d • D) = d ^ 3 •
      ![lineThird W P D d 0, W.toProjective.negY (lineThird W P D d),
        lineThird W P D d 2] := by
  rw [projectiveAdd_eq_negThird, lineThird_compatibility W hP hd]
  ext i
  fin_cases i <;> simp [Projective.negY_smul]

/-- The two Y-chart addition formulas agree up to the explicit integral scale. -/
theorem infinityAdditionXYZ_scaled {x₁ x₂ z₁ z₂ m : R}
    (h₁ : W.toProjective.Equation ![x₁, 1, z₁])
    (hl : m * (x₂ - x₁) = z₂ - z₁)
    (hc : m * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁) :
    W.toProjective.addXYZ ![x₁, 1, z₁] ![x₂, 1, z₂] =
      (x₂ - x₁) ^ 3 • infinityAdditionXYZ W x₁ x₂ z₁ m := by
  have hq : ![x₂, 1, z₂] = ![x₁, 1, z₁] + (x₂ - x₁) • ![1, 0, m] := by
    ext i
    fin_cases i
    · change x₂ = x₁ + (x₂ - x₁) * 1
      ring
    · change (1 : R) = 1 + (x₂ - x₁) * 0
      ring
    · change z₂ = z₁ + (x₂ - x₁) * m
      linear_combination -hl
  rw [hq]
  exact projectiveAdd_on_line W h₁ (infinity_line_relation W hl hc)

end FLT.Mazur.WeierstrassIntegralChart
