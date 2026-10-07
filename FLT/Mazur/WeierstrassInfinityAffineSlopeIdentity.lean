/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# Integral slope transition across the affine and Y charts

Clearing only the two input Y coordinates gives a polynomial identity for
an arbitrary affine direction (p,q). The line and divided-cubic relations
then determine the infinity slope even on the diagonal. Both ordinary
(p = 1) and reciprocal (q = 1) directions are included.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity slope numerator multiplied by the square of both input Y coordinates. -/
def infinityAffineNumerator (x₁ x₂ y₁ y₂ : R) : R :=
  x₁ ^ 2 * y₂ ^ 2 + x₁ * x₂ * y₁ * y₂ + x₂ ^ 2 * y₁ ^ 2 +
    W.a₂ * (x₁ * y₂ ^ 2 + x₂ * y₁ * y₂) + W.a₄ * y₂ ^ 2 - W.a₁ * y₁ * y₂ ^ 2

/-- The infinity slope denominator with the same input-only denominators cleared. -/
def infinityAffineDenominator (x₂ y₁ y₂ : R) : R :=
  y₁ ^ 2 * y₂ ^ 2 + W.a₁ * x₂ * y₁ ^ 2 * y₂ +
    W.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂) - W.a₂ * x₂ ^ 2 * y₁ ^ 2 -
    W.a₄ * x₂ * (y₁ * y₂ + y₁ ^ 2) - W.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2)

/-- An integral certificate comparing the two slope numerators and denominators. -/
theorem infinityAffineSlope_identity (x₁ x₂ y₁ y₂ p q : R) :
    q * infinityAffineDenominator W x₂ y₁ y₂ +
        (p * y₁ - q * x₁) * infinityAffineNumerator W x₁ x₂ y₁ y₂ =
      q * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2) *
          (y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ -
            (x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)) -
        y₁ ^ 3 * (q * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) -
          p * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)) +
        (q * (x₁ - x₂) - p * (y₁ - y₂)) * y₁ *
          (-W.a₁ * y₂ * y₁ - W.a₁ * y₁ ^ 2 + W.a₂ * x₂ * y₁ +
            W.a₂ * y₂ * x₁ + W.a₂ * x₁ * y₁ + W.a₄ * y₂ + W.a₄ * y₁ +
            x₂ * x₁ * y₁ + y₂ * x₁ ^ 2 + x₁ ^ 2 * y₁) := by
  unfold infinityAffineDenominator infinityAffineNumerator
  ring

/-- The transition relation follows without cancelling either difference of inputs. -/
theorem infinityAffineSlope_relation {x₁ x₂ y₁ y₂ p q : R}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (hl : q * (x₁ - x₂) = p * (y₁ - y₂))
    (hc : q * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      p * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁)) :
    q * infinityAffineDenominator W x₂ y₁ y₂ +
      (p * y₁ - q * x₁) * infinityAffineNumerator W x₁ x₂ y₁ y₂ = 0 := by
  rw [infinityAffineSlope_identity]
  rw [Affine.equation_iff] at h₁
  rw [h₁, sub_self, hc, sub_self, hl, sub_self]
  ring

/-- On the infinity slope open, the direction transforms by its affine intercept. -/
theorem infinityAffineSlope_intercept {x₁ x₂ y₁ y₂ p q m : R}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (hl : q * (x₁ - x₂) = p * (y₁ - y₂))
    (hc : q * (y₁ + y₂ + W.a₁ * x₂ + W.a₃) =
      p * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁))
    (hu : IsUnit (infinityAffineDenominator W x₂ y₁ y₂))
    (hm : m * infinityAffineDenominator W x₂ y₁ y₂ =
      infinityAffineNumerator W x₁ x₂ y₁ y₂) :
    m * (p * y₁ - q * x₁) = -q := by
  apply hu.mul_right_inj.mp
  linear_combination (p * y₁ - q * x₁) * hm + infinityAffineSlope_relation W h₁ hl hc

/-- For an ordinary direction, invertible input Y forces an invertible intercept. -/
theorem infinityAffineSlope_ordinary_intercept_isUnit {x y l m : R}
    (hy : IsUnit y) (hm : m * (y - l * x) = -l) : IsUnit (y - l * x) := by
  have h : (y - l * x) * (1 - m * x) = y := by linear_combination -x * hm
  exact isUnit_of_mul_isUnit_left (h.symm ▸ hy)

/-- For a reciprocal direction the slope relation itself forces the intercept to be a unit. -/
theorem infinityAffineSlope_reciprocal_intercept_isUnit {x y r m : R}
    (hm : m * (r * y - x) = -1) : IsUnit (r * y - x) := by
  exact isUnit_of_mul_isUnit_right (hm.symm ▸ isUnit_neg_one)

end FLT.Mazur.WeierstrassIntegralChart
