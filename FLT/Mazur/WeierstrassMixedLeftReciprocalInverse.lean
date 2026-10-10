/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalCenteredCubics
public import FLT.Mazur.WeierstrassMixedTripleSlopes

/-!
# The reciprocal left outer slope has an explicit inverse

The right ordinary chart forces the left reciprocal output into its affine locus.
Both outer laws may independently use their secant or tangent denominator.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Actual reciprocal-left and ordinary-right laws force an invertible left slope. -/
theorem mixed_left_reciprocal_inverse {x₁ x₂ x₃ y₁ y₂ y₃ l m n o : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hcl : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
    (hcm : m * (y₂ + y₃ + W.a₁ * x₃ + W.a₃) =
      x₂ ^ 2 + x₂ * x₃ + x₃ ^ 2 + W.a₂ * (x₂ + x₃) + W.a₄ - W.a₁ * y₂)
    (hn : n * (W.toAffine.addY x₁ x₂ y₁ l - y₃) = W.toAffine.addX x₁ x₂ l - x₃)
    (ho : o * (x₁ - W.toAffine.addX x₂ x₃ m) = y₁ - W.toAffine.addY x₂ x₃ y₂ m)
    (hcn : n * ((W.toAffine.addX x₁ x₂ l) ^ 2 +
        W.toAffine.addX x₁ x₂ l * x₃ + x₃ ^ 2 +
        W.a₂ * (W.toAffine.addX x₁ x₂ l + x₃) + W.a₄ -
        W.a₁ * W.toAffine.addY x₁ x₂ y₁ l) =
      W.toAffine.addY x₁ x₂ y₁ l + y₃ + W.a₁ * x₃ + W.a₃)
    (hco : o * (y₁ + W.toAffine.addY x₂ x₃ y₂ m + W.a₁ * W.toAffine.addX x₂ x₃ m + W.a₃) =
      x₁ ^ 2 + x₁ * W.toAffine.addX x₂ x₃ m + (W.toAffine.addX x₂ x₃ m) ^ 2 +
        W.a₂ * (x₁ + W.toAffine.addX x₂ x₃ m) + W.a₄ - W.a₁ * y₁)
    (hd : IsUnit (W.toAffine.addY x₁ x₂ y₁ l - y₃) ∨
      IsUnit ((W.toAffine.addX x₁ x₂ l) ^ 2 + W.toAffine.addX x₁ x₂ l * x₃ + x₃ ^ 2 +
        W.a₂ * (W.toAffine.addX x₁ x₂ l + x₃) + W.a₄ -
        W.a₁ * W.toAffine.addY x₁ x₂ y₁ l))
    (he : IsUnit (x₁ - W.toAffine.addX x₂ x₃ m) ∨
      IsUnit (y₁ + W.toAffine.addY x₂ x₃ y₂ m + W.a₁ * W.toAffine.addX x₂ x₃ m + W.a₃)) :
    n * (o + m - l) = 1 := by
  have hu : W.toAffine.addX x₁ x₂ l - x₂ =
      l ^ 2 + W.a₁ * l - (W.a₂ + 3 * x₂) - (x₁ - x₂) := by
    simp only [Affine.addX]
    ring
  have hv : W.toAffine.addX x₂ x₃ m - x₂ =
      m ^ 2 + W.a₁ * m - (W.a₂ + 3 * x₂) - (x₃ - x₂) := by
    simp only [Affine.addX]
    ring
  rw [reciprocal_left_denominator_centered W hl hm,
    reciprocal_left_cubic_denominator_centered W hl] at hd
  have hn' := hn
  rw [reciprocal_left_denominator_centered W hl hm] at hn'
  have hnc : n * (-(l + W.a₁) * (W.toAffine.addX x₁ x₂ l - x₂) -
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) - m * (x₃ - x₂)) =
      (W.toAffine.addX x₁ x₂ l - x₂) - (x₃ - x₂) := by
    linear_combination hn'
  have he' : IsUnit ((x₁ - x₂) - (W.toAffine.addX x₂ x₃ m - x₂)) ∨
      IsUnit (l * (x₁ - x₂) - m * (W.toAffine.addX x₂ x₃ m - x₂)) := by
    rcases he with he | he
    · left
      convert he using 1
      ring
    · right
      convert he using 1
      simp only [Affine.addY, Affine.negY, Affine.negAddY]
      linear_combination hl
  have hzv := triple_last_product W.toAffine hm hcm
  have ht := reciprocal_triple_left_parameter_of_cubic hu hv
    (triple_first_product W.toAffine hl hcl) hzv hnc
    (reciprocal_left_cubic_centered W hl hm hcn) hd
  exact mixed_triple_left_inverse hu hv hzv hnc (triple_right_line_centered W.toAffine hl ho)
    (triple_right_cubic_centered W.toAffine hl hco) ht he'

end FLT.Mazur.WeierstrassIntegralAddition
