/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalAdditionFormula
public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# Integral slope identities under input interchange

The ordinary, reciprocal and infinity formulas are symmetric when their
line relation holds. Their divided-difference relations also survive input
interchange; no cancellation of an input difference is needed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- An ordinary slope satisfies the divided-difference relation in the opposite order. -/
theorem ordinarySlope_cubic_swap {x₁ x₂ y₁ y₂ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hc : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) :
    l * (y₂ + y₁ + W.a₁ * x₁ + W.a₃) =
      x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2 + W.a₂ * (x₂ + x₁) + W.a₄ - W.a₁ * y₂ := by
  linear_combination hc + W.a₁ * hl

/-- With its line relation, ordinary addition is symmetric in both points. -/
theorem ordinaryAdditionXYZ_swap {x₁ x₂ y₁ y₂ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂) :
    ![W.toAffine.addX x₂ x₁ l, W.toAffine.addY x₂ x₁ y₂ l, (1 : R)] =
      ![W.toAffine.addX x₁ x₂ l, W.toAffine.addY x₁ x₂ y₁ l, (1 : R)] := by
  ext i
  fin_cases i <;> dsimp [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY]
  · ring
  · linear_combination -hl

/-- The reciprocal divided-difference relation also survives input interchange. -/
theorem reciprocalSlope_cubic_swap {x₁ x₂ y₁ y₂ m : R}
    (hl : m * (y₁ - y₂) = x₁ - x₂)
    (hc : m *
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) =
      y₁ + y₂ + W.a₁ * x₂ + W.a₃) :
    m * (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2 + W.a₂ * (x₂ + x₁) + W.a₄ - W.a₁ * y₂) =
      y₂ + y₁ + W.a₁ * x₁ + W.a₃ := by
  linear_combination hc + W.a₁ * hl

/-- The homogeneous reciprocal output is symmetric, including vertical chords. -/
theorem reciprocalAdditionXYZ_swap {x₁ x₂ y₁ y₂ m : R}
    (hl : m * (y₁ - y₂) = x₁ - x₂) :
    reciprocalXYZ W x₂ x₁ y₂ m = reciprocalXYZ W x₁ x₂ y₁ m := by
  ext i
  fin_cases i <;> dsimp [reciprocalXYZ, reciprocalH]
  · ring
  · linear_combination m ^ 2 * hl

/-- The infinity divided difference has the same slope in the opposite input order. -/
theorem infinitySlope_cubic_swap {x₁ x₂ z₁ z₂ m : R}
    (hl : m * (x₂ - x₁) = z₂ - z₁)
    (hc : m * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁) :
    m * infinitySlopeDenominator W x₁ z₂ z₁ =
      infinitySlopeNumerator W x₂ x₁ z₂ := by
  dsimp only [infinitySlopeDenominator, infinitySlopeNumerator] at hc ⊢
  linear_combination hc + (W.a₂ * (x₁ + x₂) + W.a₄ * (z₁ + z₂) - W.a₁) * hl

/-- The regular infinity output is symmetric whenever its line relation holds. -/
theorem infinityAdditionXYZ_swap {x₁ x₂ z₁ z₂ m : R}
    (hl : m * (x₂ - x₁) = z₂ - z₁) :
    infinityAdditionXYZ W x₂ x₁ z₂ m = infinityAdditionXYZ W x₁ x₂ z₁ m := by
  have hz : z₂ = z₁ + m * (x₂ - x₁) := by linear_combination -hl
  rw [hz]
  ext i
  fin_cases i <;>
    simp [infinityAdditionXYZ, lineThird, cubicPolar, Projective.negY,
      Projective.eval_polynomial] <;> ring

end FLT.Mazur.WeierstrassIntegralChart
