/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityVietaComparison

/-!
# Full-domain comparison of infinity and affine addition formulas

The ordinary and reciprocal formulas compare by the cube of the affine
intercept and the product of input Y coordinates. These are units on the
actual common domain; no factor vanishing on the diagonal is used.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x₁ x₂ y₁ y₂ u v m : R}

/-- Ordinary addition and infinity addition have an integral full-domain scaling identity. -/
theorem infinityAffine_ordinary_formula {l : R}
    (hP : W.toAffine.Equation x₁ y₁)
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hc : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
    (hu : u * y₁ = 1) (hv : v * y₂ = 1) (hm : m * (y₁ - l * x₁) = -l) :
    (y₁ - l * x₁) ^ 3 • infinityAdditionXYZ W (x₁ * u) (x₂ * v) u m =
      (-(y₁ * y₂)) • ![W.toAffine.addX x₁ x₂ l, W.toAffine.addY x₁ x₂ y₁ l, 1] := by
  have h := infinityVieta_addition W hP (ordinaryVieta_relation W hl hc)
    (by ring : x₂ = x₁ + (x₂ - x₁) * 1)
    (by linear_combination hl : y₂ = y₁ + (x₂ - x₁) * l) hu hv
    (by simpa only [one_mul] using hm)
  simpa only [one_mul, ordinaryVieta_formula, smul_smul, mul_neg_one] using h

/-- Reciprocal addition has the same comparison, also when its slope is zero. -/
theorem infinityAffine_reciprocal_formula {r : R}
    (hP : W.toAffine.Equation x₁ y₁)
    (hl : r * (y₁ - y₂) = x₁ - x₂)
    (hc : r * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) =
      y₁ + y₂ + W.a₁ * x₂ + W.a₃)
    (hu : u * y₁ = 1) (hv : v * y₂ = 1) (hm : m * (r * y₁ - x₁) = -1) :
    (r * y₁ - x₁) ^ 3 • infinityAdditionXYZ W (x₁ * u) (x₂ * v) u m =
      (-(y₁ * y₂)) • reciprocalXYZ W x₁ x₂ y₁ r := by
  have h := infinityVieta_addition W hP (reciprocalVieta_relation W hl hc)
    (by linear_combination hl : x₂ = x₁ + (y₂ - y₁) * r)
    (by ring : y₂ = y₁ + (y₂ - y₁) * 1) hu hv
    (by simpa only [one_mul] using hm)
  simpa only [one_mul, reciprocalVieta_formula W hl, smul_smul, mul_neg_one] using h

end FLT.Mazur.WeierstrassIntegralChart
