/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalTripleCoordinates

/-!
# Ordinary inner additions and reciprocal outer secants

The four actual line relations and two inner divided differences determine an
invertible comparison of homogeneous outputs. Reciprocal slopes may be zero.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Reciprocal secant outer laws give the same projective triple output. -/
theorem reciprocal_secant_triple_coordinates {x₁ x₂ x₃ y₁ y₂ y₃ l m r s : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hm : m * (x₂ - x₃) = y₂ - y₃)
    (hcl : l * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)
    (hcm : m * (y₂ + y₃ + W.a₁ * x₃ + W.a₃) =
      x₂ ^ 2 + x₂ * x₃ + x₃ ^ 2 + W.a₂ * (x₂ + x₃) + W.a₄ - W.a₁ * y₂)
    (hn : r * (W.toAffine.addY x₁ x₂ y₁ l - y₃) = W.toAffine.addX x₁ x₂ l - x₃)
    (ho : s * (y₁ - W.toAffine.addY x₂ x₃ y₂ m) = x₁ - W.toAffine.addX x₂ x₃ m)
    (hd : IsUnit (W.toAffine.addY x₁ x₂ y₁ l - y₃))
    (he : IsUnit (y₁ - W.toAffine.addY x₂ x₃ y₂ m)) :
    IsUnit (1 + (l - m) * r) ∧ ∀ i : Fin 3,
      reciprocalXYZ W (W.toAffine.addX x₁ x₂ l) x₃
          (W.toAffine.addY x₁ x₂ y₁ l) r i =
        (1 + (l - m) * r) ^ 3 *
          reciprocalXYZ W x₁ (W.toAffine.addX x₂ x₃ m) y₁ s i := by
  have hu : W.toAffine.addX x₁ x₂ l - x₂ =
      l ^ 2 + W.a₁ * l - (W.a₂ + 3 * x₂) - (x₁ - x₂) := by
    simp only [Affine.addX]
    ring
  have hv : W.toAffine.addX x₂ x₃ m - x₂ =
      m ^ 2 + W.a₁ * m - (W.a₂ + 3 * x₂) - (x₃ - x₂) := by
    simp only [Affine.addX]
    ring
  have hn' := hn
  have ho' := ho
  rw [reciprocal_left_denominator_centered W hl hm] at hn' hd
  rw [reciprocal_right_denominator_centered W hl] at ho' he
  have hnl : r * (-(l + W.a₁) * (W.toAffine.addX x₁ x₂ l - x₂) -
        (W.a₃ + W.a₁ * x₂ + 2 * y₂) - m * (x₃ - x₂)) =
      (W.toAffine.addX x₁ x₂ l - x₂) - (x₃ - x₂) := by
    linear_combination hn'
  have hor : s * (l * (x₁ - x₂) +
        (m + W.a₁) * (W.toAffine.addX x₂ x₃ m - x₂) +
        (W.a₃ + W.a₁ * x₂ + 2 * y₂)) =
      (x₁ - x₂) - (W.toAffine.addX x₂ x₃ m - x₂) := by
    linear_combination ho'
  have ht := reciprocal_triple_left_parameter hu hv
    (triple_inner_cross W.toAffine hl hm hcl hcm) hnl hd
  have hs := reciprocal_triple_outer_slopes hu hv hnl hor ht he
  refine ⟨reciprocal_triple_scale_isUnit hs, ?_⟩
  apply reciprocal_triple_coordinates W hl hm hn _ hs
  linear_combination ht

end FLT.Mazur.WeierstrassIntegralAddition
