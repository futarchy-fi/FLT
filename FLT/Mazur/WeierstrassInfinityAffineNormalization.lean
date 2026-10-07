/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAffineSlopeIdentity

/-!
# Normalizing the integral slope transition

Only the two input Y coordinates are inverted. Explicit ring certificates
identify the cleared numerator and denominator with the actual infinity
slope expressions; no difference of inputs or output polynomial is cancelled.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x₁ x₂ y₁ y₂ u v : R}

/-- The cleared numerator is the actual Y-chart numerator times the input unit factor. -/
theorem infinityAffineNumerator_normalize (hu : u * y₁ = 1) (hv : v * y₂ = 1) :
    infinityAffineNumerator W x₁ x₂ y₁ y₂ =
      y₁ ^ 2 * y₂ ^ 2 * infinitySlopeNumerator W (x₁ * u) (x₂ * v) u := by
  unfold infinityAffineNumerator infinitySlopeNumerator
  linear_combination
    -y₂ ^ 2 * (-W.a₁ * y₁ + W.a₂ * v * x₂ * y₁ + W.a₂ * u * x₁ * y₁ +
      W.a₂ * x₁ + W.a₄ * u * y₁ + W.a₄ + v * x₂ * x₁ * y₁ +
      u * x₁ ^ 2 * y₁ + x₁ ^ 2) * hu -
    x₂ * y₁ * (W.a₂ * y₂ + v * x₂ * y₂ * y₁ + x₂ * y₁ + y₂ * x₁) * hv

/-- The cleared denominator is the actual Y-chart denominator times the same factor. -/
theorem infinityAffineDenominator_normalize (hu : u * y₁ = 1) (hv : v * y₂ = 1) :
    infinityAffineDenominator W x₂ y₁ y₂ =
      y₁ ^ 2 * y₂ ^ 2 * infinitySlopeDenominator W (x₂ * v) u v := by
  unfold infinityAffineDenominator infinitySlopeDenominator
  linear_combination
    y₂ ^ 2 * (-W.a₃ * y₁ + W.a₄ * v * x₂ * y₁ + W.a₆ * v * y₁ +
      W.a₆ * u * y₁ + W.a₆) * hu +
    y₁ * (-W.a₁ * x₂ * y₂ * y₁ + W.a₂ * v * x₂ ^ 2 * y₂ * y₁ +
      W.a₂ * x₂ ^ 2 * y₁ - W.a₃ * y₂ * y₁ + W.a₄ * v * x₂ * y₂ * y₁ +
      W.a₄ * x₂ * y₂ + W.a₄ * x₂ * y₁ + W.a₆ * v * y₂ * y₁ +
      W.a₆ * y₂ + W.a₆ * y₁) * hv

/-- The slope transition expressed directly in the normalized Y-chart coordinates. -/
theorem infinityAffineSlope_normalized {p q m : R}
    (hu : u * y₁ = 1) (hv : v * y₂ = 1)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (hl : q * (x₁ - x₂) = p * (y₁ - y₂))
    (hc : q * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      p * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁))
    (hd : IsUnit (infinitySlopeDenominator W (x₂ * v) u v))
    (hm : m * infinitySlopeDenominator W (x₂ * v) u v =
      infinitySlopeNumerator W (x₁ * u) (x₂ * v) u) :
    m * (p * y₁ - q * x₁) = -q := by
  have hy₁ : IsUnit y₁ := isUnit_of_mul_isUnit_right (hu.symm ▸ isUnit_one)
  have hy₂ : IsUnit y₂ := isUnit_of_mul_isUnit_right (hv.symm ▸ isUnit_one)
  apply infinityAffineSlope_intercept W h₁ hl hc
  · rw [infinityAffineDenominator_normalize W hu hv]
    exact ((hy₁.pow 2).mul (hy₂.pow 2)).mul hd
  · rw [infinityAffineDenominator_normalize W hu hv,
      infinityAffineNumerator_normalize W hu hv]
    linear_combination y₁ ^ 2 * y₂ ^ 2 * hm

end FLT.Mazur.WeierstrassIntegralChart
