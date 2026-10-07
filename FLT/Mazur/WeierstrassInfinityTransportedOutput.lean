/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTransportedSlopes
public import FLT.Mazur.WeierstrassInfinityAffineFormula
public import FLT.Mazur.WeierstrassAdditionOutputFamilies

/-!
# Homogeneous infinity outputs on the full affine intersection

Restrict the existing infinity formula, its output unit and normalization
identity to the actual intersection. The ordinary affine law has the same
homogeneous output up to the input-unit and intercept factors.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i : AdditionChartIndex)

/-- The existing homogeneous infinity output restricted to the full intersection. -/
def infinityTransportedCoordinates : Fin 3 → InfinityTransportedIntersection W i :=
  infinityTransportedSlopeRestriction W i ∘ infinityOutputCoordinates W

/-- Its formula uses exactly the common original input coordinates and regular slope. -/
theorem infinityTransportedCoordinates_eq :
    infinityTransportedCoordinates W i =
      infinityAdditionXYZ (W.map (algebraMap R (InfinityTransportedIntersection W i)))
        (infinityLeft W (infinityTransportedInput W i) 0)
        (infinityRight W (infinityTransportedInput W i) 0)
        (infinityLeft W (infinityTransportedInput W i) 2) (infinityTransportedSlope W i) := by
  let f := infinityTransportedSlopeRestriction W i
  have he : (W.map (algebraMap R (InfinitySlopeOpen W))).map f.toRingHom =
      W.map (algebraMap R (InfinityTransportedIntersection W i)) := by
    ext <;> exact f.commutes _
  change f.toRingHom ∘ infinityAdditionXYZ _ _ _ _ _ = _
  rw [infinityAdditionXYZ_map, he]
  rfl

/-- The infinity output Y remains a unit on the full intersection. -/
theorem infinityTransportedCoordinates_y_isUnit : IsUnit (infinityTransportedCoordinates W i 1) :=
  (infinityOutputY_isUnit W).map (infinityTransportedInfinity W i)

/-- The existing normalized infinity addition map on the full intersection. -/
def infinityTransportedAddition : Coordinate W 1 →ₐ[R] InfinityTransportedIntersection W i :=
  (infinityTransportedInfinity W i).comp (infinityAdditionChart W)

/-- Clearing the actual output Y recovers the restricted homogeneous formula. -/
theorem infinityTransportedAddition_mul (a : Fin 3) :
    infinityTransportedAddition W i (coord W 1 a) * infinityTransportedCoordinates W i 1 =
      infinityTransportedCoordinates W i a := by
  exact (map_mul _ _ _).symm.trans
    (congrArg (infinityTransportedInfinity W i) (infinityAdditionChart_mul W a))

/-- The negative product of normalized input Y coordinates. -/
def infinityTransportedInputFactor : InfinityTransportedIntersection W i :=
  -(infinityTransportedNormalized W i (productY₁ W) *
    infinityTransportedNormalized W i (productY₂ W))

/-- This factor is a unit everywhere on the full intersection. -/
theorem infinityTransportedInputFactor_isUnit : IsUnit (infinityTransportedInputFactor W i) :=
  ((isUnit_of_mul_isUnit_right ((infinityTransported_left_inverse W i).symm ▸ isUnit_one)).mul
    (isUnit_of_mul_isUnit_right ((infinityTransported_right_inverse W i).symm ▸ isUnit_one))).neg

variable (b : Bool)

/-- Intercept of the ordinary affine line in the actual intersection ring. -/
def infinityTransportedOrdinaryIntercept : InfinityTransportedIntersection W (ordinaryIndex b) :=
  infinityTransportedNormalized W (ordinaryIndex b) (productY₁ W) -
    infinityTransportedChart W (ordinaryIndex b) (ordinaryChartSlope W b) *
      infinityTransportedNormalized W (ordinaryIndex b) (productX₁ W)

/-- Ordinary and infinity homogeneous outputs agree up to units on the entire intersection. -/
theorem infinityTransported_ordinary_output (a : Fin 3) :
    infinityTransportedOrdinaryIntercept W b ^ 3 *
        infinityTransportedCoordinates W (ordinaryIndex b) a =
      infinityTransportedInputFactor W (ordinaryIndex b) *
        infinityTransportedChart W (ordinaryIndex b) (ordinaryChartAddition W b (coord W 2 a)) := by
  let f := infinityTransportedNormalized W (ordinaryIndex b)
  let g := infinityTransportedChart W (ordinaryIndex b)
  have hl := congrArg g (ordinaryChartSlope_line W b)
  have hc := congrArg g (ordinaryChartSlope_cubic W b)
  simp only [map_mul, map_secantDenominator, map_verticalSecantDenominator, map_sub] at hl
  simp only [map_mul, map_tangentDenominator, map_tangentNumerator, map_add, map_sub,
    map_pow, AlgHom.commutes] at hc
  have hs := infinityAffine_ordinary_formula
    (W.map (algebraMap R (InfinityTransportedIntersection W (ordinaryIndex b))))
    (productLeft_equation W f) hl hc
    (infinityTransported_left_inverse W (ordinaryIndex b))
    (infinityTransported_right_inverse W (ordinaryIndex b))
    (infinityTransported_ordinary_slope W b)
  change infinityTransportedOrdinaryIntercept W b ^ 3 •
    infinityAdditionXYZ _
      (f (productX₁ W) * infinityLeft W (infinityTransportedInput W (ordinaryIndex b)) 2)
      (f (productX₂ W) * infinityRight W (infinityTransportedInput W (ordinaryIndex b)) 2)
      _ _ = _ at hs
  rw [infinityTransported_left_x, infinityTransported_right_x,
    ← infinityTransportedCoordinates_eq] at hs
  rw [ordinaryChartAddition_map_coord]
  exact congrFun hs a

end FLT.Mazur.WeierstrassIntegralChart
