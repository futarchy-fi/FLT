/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTransportedOutput

/-!
# Reciprocal addition outputs on the full infinity intersection

The reciprocal affine formula and infinity formula differ by units on their
full common domain. Their existing normalized Y-chart algebra maps therefore
agree there, including on the polynomial base locus and vertical tangents.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b : Bool)

/-- Intercept of the reciprocal affine line in the full intersection ring. -/
def infinityTransportedReciprocalIntercept :
    InfinityTransportedIntersection W (reciprocalIndex b) :=
  infinityTransportedChart W (reciprocalIndex b) (reciprocalChartSlope W b) *
      infinityTransportedNormalized W (reciprocalIndex b) (productY₁ W) -
    infinityTransportedNormalized W (reciprocalIndex b) (productX₁ W)

/-- The reciprocal homogeneous coordinates after restriction to the full intersection. -/
def infinityTransportedReciprocalCoordinates (a : Fin 3) :
    InfinityTransportedIntersection W (reciprocalIndex b) :=
  infinityTransportedChart W (reciprocalIndex b)
    (reciprocalCoordinates W (additionChartAlgRestriction W (reciprocalIndex b))
      (reciprocalChartSlope W b) a)

/-- Reciprocal and infinity homogeneous outputs agree up to units on their full intersection. -/
theorem infinityTransported_reciprocal_output (a : Fin 3) :
    infinityTransportedReciprocalIntercept W b ^ 3 *
        infinityTransportedCoordinates W (reciprocalIndex b) a =
      infinityTransportedInputFactor W (reciprocalIndex b) *
        infinityTransportedReciprocalCoordinates W b a := by
  let f := infinityTransportedNormalized W (reciprocalIndex b)
  let g := infinityTransportedChart W (reciprocalIndex b)
  have hl := congrArg g (reciprocalChartSlope_line W b)
  have hc := congrArg g (reciprocalChartSlope_cubic W b)
  simp only [map_mul, map_secantDenominator, map_verticalSecantDenominator, map_sub] at hl
  simp only [map_mul, map_tangentDenominator, map_tangentNumerator, map_add, map_sub,
    map_pow, AlgHom.commutes] at hc
  have hs := infinityAffine_reciprocal_formula
    (W.map (algebraMap R (InfinityTransportedIntersection W (reciprocalIndex b))))
    (productLeft_equation W f) hl hc
    (infinityTransported_left_inverse W (reciprocalIndex b))
    (infinityTransported_right_inverse W (reciprocalIndex b))
    (infinityTransported_reciprocal_slope W b)
  change infinityTransportedReciprocalIntercept W b ^ 3 •
    infinityAdditionXYZ _
      (f (productX₁ W) * infinityLeft W (infinityTransportedInput W (reciprocalIndex b)) 2)
      (f (productX₂ W) * infinityRight W (infinityTransportedInput W (reciprocalIndex b)) 2)
      _ _ = _ at hs
  rw [infinityTransported_left_x, infinityTransported_right_x,
    ← infinityTransportedCoordinates_eq] at hs
  rw [infinityTransportedReciprocalCoordinates, reciprocalCoordinates_map]
  exact congrFun hs a

/-- The actual reciprocal output inverse still cancels its homogeneous Y coordinate. -/
theorem infinityTransportedReciprocalInverse_mul :
    infinityTransportedChart W (reciprocalIndex b) (reciprocalChartInverse W b) *
      infinityTransportedReciprocalCoordinates W b 1 = 1 := by
  have h := congrArg (infinityTransportedChart W (reciprocalIndex b))
    (reciprocalChartAddition_coord W b 1)
  rw [coord_self, map_one, map_one, map_mul] at h
  exact h.symm

/-- The existing normalized reciprocal map equals the existing infinity map on the full domain. -/
theorem infinityTransported_reciprocal_addition :
    (infinityTransportedChart W (reciprocalIndex b)).comp (reciprocalChartAddition W b) =
      infinityTransportedAddition W (reciprocalIndex b) := by
  apply hom_ext
  intro a
  apply (infinityTransportedCoordinates_y_isUnit W (reciprocalIndex b)).mul_left_inj.mp
  rw [infinityTransportedAddition_mul]
  apply ((infinityTransported_reciprocal_intercept_isUnit W b).pow 3).mul_right_inj.mp
  change infinityTransportedReciprocalIntercept W b ^ 3 *
    (infinityTransportedChart W (reciprocalIndex b)
      (reciprocalChartAddition W b (coord W 1 a)) *
        infinityTransportedCoordinates W (reciprocalIndex b) 1) =
      infinityTransportedReciprocalIntercept W b ^ 3 *
        infinityTransportedCoordinates W (reciprocalIndex b) a
  rw [reciprocalChartAddition_coord, map_mul]
  have h₁ := infinityTransported_reciprocal_output W b 1
  have ha := infinityTransported_reciprocal_output W b a
  have hi := infinityTransportedReciprocalInverse_mul W b
  change infinityTransportedReciprocalIntercept W b ^ 3 *
    ((infinityTransportedChart W (reciprocalIndex b) (reciprocalChartInverse W b) *
      infinityTransportedReciprocalCoordinates W b a) *
        infinityTransportedCoordinates W (reciprocalIndex b) 1) =
      infinityTransportedReciprocalIntercept W b ^ 3 *
        infinityTransportedCoordinates W (reciprocalIndex b) a
  linear_combination
    infinityTransportedChart W (reciprocalIndex b) (reciprocalChartInverse W b) *
      infinityTransportedReciprocalCoordinates W b a * h₁ - ha +
    infinityTransportedInputFactor W (reciprocalIndex b) *
      infinityTransportedReciprocalCoordinates W b a * hi

end FLT.Mazur.WeierstrassIntegralChart
