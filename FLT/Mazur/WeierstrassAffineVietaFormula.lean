/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVietaNormalization
public import FLT.Mazur.WeierstrassReciprocalAdditionFormula

/-!
# Ordinary and reciprocal affine addition as Vieta formulas

Both regular slope families satisfy the divided line-cubic relation.
Their existing output coordinates are the negated Vieta third point,
including tangent and reciprocal-slope-zero inputs.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Ordinary slope relations give the divided quadratic relation of the line cubic. -/
theorem ordinaryVieta_relation {x₁ x₂ y₁ y₂ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hc : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) :
    cubicPolar W ![x₁, y₁, 1] ![1, l, 0] +
      cubicPolar W ![1, l, 0] ![x₁, y₁, 1] * (x₂ - x₁) +
      eval ![1, l, 0] W.toProjective.polynomial * (x₂ - x₁) ^ 2 = 0 := by
  simp only [cubicPolar, Projective.eval_polynomial, Projective.fin3_def_ext]
  linear_combination hc - l * hl

/-- Reciprocal slope relations give the same divided quadratic relation. -/
theorem reciprocalVieta_relation {x₁ x₂ y₁ y₂ r : R}
    (hl : r * (y₁ - y₂) = x₁ - x₂)
    (hc : r * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) =
      y₁ + y₂ + W.a₁ * x₂ + W.a₃) :
    cubicPolar W ![x₁, y₁, 1] ![r, 1, 0] +
      cubicPolar W ![r, 1, 0] ![x₁, y₁, 1] * (y₂ - y₁) +
      eval ![r, 1, 0] W.toProjective.polynomial * (y₂ - y₁) ^ 2 = 0 := by
  simp only [cubicPolar, Projective.eval_polynomial, Projective.fin3_def_ext]
  linear_combination -hc +
    (-W.a₁ + W.a₂ * r + r ^ 2 * y₂ - r ^ 2 * y₁ + r * x₂ + 2 * r * x₁) * hl

/-- The ordinary affine law is the negative of the elliptically negated Vieta representative. -/
theorem ordinaryVieta_formula (x₁ x₂ y₁ l : R) :
    let T := lineThird W ![x₁, y₁, 1] ![1, l, 0] (x₂ - x₁)
    ![T 0, W.toProjective.negY T, T 2] =
      (-1 : R) • ![W.toAffine.addX x₁ x₂ l, W.toAffine.addY x₁ x₂ y₁ l, 1] := by
  ext i
  fin_cases i <;>
    simp only [lineThird, cubicPolar, Projective.eval_polynomial, Projective.negY,
      Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Projective.fin3_def_ext] <;> dsimp <;> ring

/-- The reciprocal law has the same Vieta description without inverting its slope. -/
theorem reciprocalVieta_formula {x₁ x₂ y₁ y₂ r : R}
    (hl : r * (y₁ - y₂) = x₁ - x₂) :
    let T := lineThird W ![x₁, y₁, 1] ![r, 1, 0] (y₂ - y₁)
    ![T 0, W.toProjective.negY T, T 2] = (-1 : R) • reciprocalXYZ W x₁ x₂ y₁ r := by
  ext i
  fin_cases i <;>
    simp only [lineThird, cubicPolar, Projective.eval_polynomial, Projective.negY,
      reciprocalXYZ, reciprocalH, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Projective.fin3_def_ext] <;> dsimp
  · linear_combination -r ^ 3 * hl
  · linear_combination r ^ 2 * (W.a₁ * r + 1) * hl
  · ring

end FLT.Mazur.WeierstrassIntegralChart
