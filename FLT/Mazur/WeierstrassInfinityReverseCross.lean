/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInnerCross

/-!
# The reverse inner-secant cross relation

Reverse both secants before applying the common-center comparison. The result
controls the second inner output at the first input, including coincident inputs.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x₁ x₂ x₃ z₁ z₂ z₃ l m : R}

/-- Reversing the input triple gives the complementary homogeneous cross relation. -/
theorem infinity_inner_cross_reverse
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂) :
    (x₃ - x₁) *
        (infinityLineLeading W m * x₁ - infinityAdditionXYZ W x₂ x₃ z₂ m 0) =
      (l - m) * infinitySlopeDenominator W x₁ (z₂ + m * (x₁ - x₂)) z₁ := by
  have hl' : l * (x₁ - x₂) = z₁ - z₂ := by linear_combination -hl
  have hm' : m * (x₂ - x₃) = z₂ - z₃ := by linear_combination -hm
  have h := infinity_inner_cross W hm' hl'
    (infinitySlope_cubic_swap W hm hcm) (infinitySlope_cubic_swap W hl hcl)
  rw [infinityAdditionXYZ_swap W hm] at h
  linear_combination -h

/-- The reverse comparison clears only the second inner output's actual Y normalizer. -/
theorem infinity_inner_cross_reverse_normalized {u v c : R}
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂)
    (hx : u * c = infinityAdditionXYZ W x₂ x₃ z₂ m 0)
    (hn : (-1 - W.a₁ * u - W.a₃ * v) * c = infinityLineLeading W m) :
    c * (x₃ - x₁) * ((-1 - W.a₁ * u - W.a₃ * v) * x₁ - u) =
      (l - m) * infinitySlopeDenominator W x₁ (z₂ + m * (x₁ - x₂)) z₁ := by
  have h := infinity_inner_cross_reverse W hl hm hcl hcm
  rw [← hx, ← hn] at h
  linear_combination h

end FLT.Mazur.WeierstrassIntegralChart
