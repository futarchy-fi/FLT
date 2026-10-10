/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalCenteredCubics
public import FLT.Mazur.WeierstrassMixedTripleSlopes

/-!
# The reciprocal right outer slope has an explicit inverse

Center the actual chart relations, keeping either secant or tangent unit on each
outer chart. The ordinary left output forces the right output into the affine locus.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Actual ordinary-left and reciprocal-right outer laws force an invertible right slope. -/
theorem mixed_right_reciprocal_inverse {x₁ x₂ x₃ y₁ y₂ y₃ l m n o : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hcl : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
    (hcm : m * (y₂ + y₃ + W.a₁ * x₃ + W.a₃) =
      x₂ ^ 2 + x₂ * x₃ + x₃ ^ 2 + W.a₂ * (x₂ + x₃) + W.a₄ - W.a₁ * y₂)
    (hn : n * (W.toAffine.addX x₁ x₂ l - x₃) = W.toAffine.addY x₁ x₂ y₁ l - y₃)
    (ho : o * (y₁ - W.toAffine.addY x₂ x₃ y₂ m) = x₁ - W.toAffine.addX x₂ x₃ m)
    (hcn : n * (W.toAffine.addY x₁ x₂ y₁ l + y₃ + W.a₁ * x₃ + W.a₃) =
      (W.toAffine.addX x₁ x₂ l) ^ 2 + W.toAffine.addX x₁ x₂ l * x₃ + x₃ ^ 2 +
        W.a₂ * (W.toAffine.addX x₁ x₂ l + x₃) + W.a₄ - W.a₁ * W.toAffine.addY x₁ x₂ y₁ l)
    (hco : o * (x₁ ^ 2 + x₁ * W.toAffine.addX x₂ x₃ m +
        (W.toAffine.addX x₂ x₃ m) ^ 2 +
        W.a₂ * (x₁ + W.toAffine.addX x₂ x₃ m) + W.a₄ - W.a₁ * y₁) =
      y₁ + W.toAffine.addY x₂ x₃ y₂ m +
        W.a₁ * W.toAffine.addX x₂ x₃ m + W.a₃)
    (hd : IsUnit (W.toAffine.addX x₁ x₂ l - x₃) ∨
      IsUnit (W.toAffine.addY x₁ x₂ y₁ l + y₃ + W.a₁ * x₃ + W.a₃))
    (he : IsUnit (y₁ - W.toAffine.addY x₂ x₃ y₂ m) ∨
      IsUnit (x₁ ^ 2 + x₁ * W.toAffine.addX x₂ x₃ m +
        (W.toAffine.addX x₂ x₃ m) ^ 2 +
        W.a₂ * (x₁ + W.toAffine.addX x₂ x₃ m) + W.a₄ - W.a₁ * y₁)) :
    o * (n + l - m) = 1 := by
  have hu : W.toAffine.addX x₁ x₂ l - x₂ =
      l ^ 2 + W.a₁ * l - (W.a₂ + 3 * x₂) - (x₁ - x₂) := by
    simp only [Affine.addX]
    ring
  have hv : W.toAffine.addX x₂ x₃ m - x₂ =
      m ^ 2 + W.a₁ * m - (W.a₂ + 3 * x₂) - (x₃ - x₂) := by
    simp only [Affine.addX]
    ring
  have hd' : IsUnit ((W.toAffine.addX x₁ x₂ l - x₂) - (x₃ - x₂)) ∨
      IsUnit (-(l + W.a₁) * (W.toAffine.addX x₁ x₂ l - x₂) + (m + W.a₁) * (x₃ - x₂)) := by
    rcases hd with hd | hd
    · left
      convert hd using 1
      ring
    · right
      convert hd using 1
      simp only [Affine.addY, Affine.negY, Affine.negAddY]
      linear_combination -hl - hm
  rw [reciprocal_right_denominator_centered W hl,
    reciprocal_right_cubic_denominator_centered W hl] at he
  have ho' := ho
  rw [reciprocal_right_denominator_centered W hl] at ho'
  have hoc : o * (l * (x₁ - x₂) +
        (m + W.a₁) * (W.toAffine.addX x₂ x₃ m - x₂) +
        (W.a₃ + W.a₁ * x₂ + 2 * y₂)) =
      (x₁ - x₂) - (W.toAffine.addX x₂ x₃ m - x₂) := by
    linear_combination ho'
  have hnc := triple_left_line_centered W.toAffine hl hm hn
  have hzv := triple_last_product W.toAffine hm hcm
  have ht := triple_left_parameter hu hv (triple_first_product W.toAffine hl hcl) hzv hnc
    (triple_left_cubic_centered W.toAffine hl hm hcn) hd'
  exact mixed_triple_right_inverse hu hv hzv hnc hoc
    (reciprocal_right_cubic_centered W hl hco) ht he

end FLT.Mazur.WeierstrassIntegralAddition
