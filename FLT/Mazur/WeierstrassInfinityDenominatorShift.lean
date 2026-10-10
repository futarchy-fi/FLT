/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityCubicDifference

/-!
# Comparing cross-line denominators with the chosen unit denominators

Changing one Z argument gives an explicit correction. A cross-line denominator
and the displacement therefore have a unit linear combination whenever the
original slope denominator is a unit. The cross denominator itself need not be.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {S : Type*} [CommRing S] (A : WeierstrassCurve S)

/-- The exact divided change in the first Z argument of a slope denominator. -/
def infinityDenominatorShiftFactor (x z w d : S) : S :=
  A.a₃ - A.a₄ * x - A.a₆ * (2 * z + w + d)

/-- The slope denominator is quadratic in each Z argument; this keeps its full correction. -/
theorem infinitySlopeDenominator_shift (x z w d : S) :
    infinitySlopeDenominator A x (z + d) w =
      infinitySlopeDenominator A x z w + d * infinityDenominatorShiftFactor A x z w d := by
  unfold infinitySlopeDenominator infinityDenominatorShiftFactor
  ring

/-- The exact change when the X argument moves while both Z arguments are held fixed. -/
theorem infinitySlopeDenominator_shift_x (x z w d : S) :
    infinitySlopeDenominator A (x + d) z w =
      infinitySlopeDenominator A x z w +
        d * (A.a₁ - A.a₂ * (2 * x + d) - A.a₄ * (z + w)) := by
  unfold infinitySlopeDenominator
  ring

/-- The correction when the endpoint moves in X and one line value moves with it. -/
def infinityDenominatorEndpointShift (x z w l d : S) : S :=
  A.a₁ - A.a₂ * (2 * x + d) - A.a₄ * (z + w) +
    l * infinityDenominatorShiftFactor A (x + d) z w (l * d)

/-- Endpoint reversal differs from the original denominator by a displacement multiple. -/
theorem infinitySlopeDenominator_endpoint_shift (x z w l d : S) :
    infinitySlopeDenominator A (x + d) (z + l * d) w -
        d * infinityDenominatorEndpointShift A x z w l d =
      infinitySlopeDenominator A x z w := by
  rw [infinitySlopeDenominator_shift, infinitySlopeDenominator_shift_x]
  unfold infinityDenominatorEndpointShift
  ring

/-- The corrected endpoint denominator inherits precisely the original unit certificate. -/
theorem infinitySlopeDenominator_endpoint_unit {x z w : S}
    (hu : IsUnit (infinitySlopeDenominator A x z w)) (l d : S) :
    IsUnit (infinitySlopeDenominator A (x + d) (z + l * d) w -
      d * infinityDenominatorEndpointShift A x z w l d) := by
  rw [infinitySlopeDenominator_endpoint_shift]
  exact hu

/-- Two line values at an endpoint differ from the chosen denominator by a known multiple. -/
theorem infinitySlopeDenominator_cross_shift (x z w l d : S) :
    infinitySlopeDenominator A x (z + l * d) w -
        d * (l * infinityDenominatorShiftFactor A x z w (l * d)) =
      infinitySlopeDenominator A x z w := by
  rw [infinitySlopeDenominator_shift]
  ring

/-- The corrected cross denominator is a certified unit, with the displacement retained. -/
theorem infinitySlopeDenominator_cross_unit {x z w : S}
    (hu : IsUnit (infinitySlopeDenominator A x z w)) (l d : S) :
    IsUnit (infinitySlopeDenominator A x (z + l * d) w -
      d * (l * infinityDenominatorShiftFactor A x z w (l * d))) := by
  rw [infinitySlopeDenominator_cross_shift]
  exact hu

/-- Simultaneous annihilation by displacement and cross denominator is sufficient. -/
theorem infinitySlopeDenominator_cross_annihilator {x z w : S}
    (hu : IsUnit (infinitySlopeDenominator A x z w)) (l d t : S)
    (hd : t * d = 0)
    (hD : t * infinitySlopeDenominator A x (z + l * d) w = 0) : t = 0 := by
  apply hu.mul_right_inj.mp
  have h := infinitySlopeDenominator_cross_shift A x z w l d
  linear_combination hD -
    (l * infinityDenominatorShiftFactor A x z w (l * d)) * hd - t * h

/-- The same exact correction is valid in homogeneous divided-cubic coordinates. -/
theorem infinityCubicDividedZ_shift (x y z w d : S) :
    infinityCubicDividedZ A x y (z + d) w =
      infinityCubicDividedZ A x y z w +
        d * (A.a₃ * y - A.a₄ * x - A.a₆ * (2 * z + w + d)) := by
  unfold infinityCubicDividedZ
  ring

end FLT.Mazur.WeierstrassIntegralChart
