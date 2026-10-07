/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityProjectiveOverlap

/-!
# Output-chart compatibility on concrete infinity intersections

On the intersection with any polynomial output open, the same coordinate of
the normalized infinity output is a unit. Changing its output chart through
the integral transition gives exactly the polynomial addition map. In
particular this compares the Y-output infinity law with the Z-output member
of the complete input cover.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (t : Fin 3)

/-- The infinity chart map restricted to the concrete intersection. -/
def infinityIntersectionChart : Coordinate W 1 →ₐ[R] InfinityProjectiveOverlap W t :=
  (infinityProjectiveRestriction W t).comp (infinityAdditionChart W)

/-- The common homogeneous scale of the polynomial and normalized infinity outputs. -/
def infinityIntersectionScale : InfinityProjectiveOverlap W t :=
  ((infinityProjectiveRestriction W t).comp (infinityOutputRestriction W))
      (infinityRight W (infinitySlopeRestriction W) 0 -
        infinityLeft W (infinitySlopeRestriction W) 0) ^ 3 *
    infinityProjectiveRestriction W t
      (infinityOutputRestriction W (infinityOutputCoordinates W 1))

/-- All polynomial output coordinates have the same scale on the concrete overlap. -/
theorem infinityIntersection_scaled (i : Fin 3) :
    infinityProjectivePolynomial W t
        (additionOutputRestriction W 1 1 t (chartProductAdditionCoordinates W 1 1 i)) =
      infinityIntersectionScale W t * infinityIntersectionChart W t (coord W 1 i) := by
  let p := (infinityProjectiveRestriction W t).comp (infinityOutputRestriction W)
  let d := infinityRight W (infinitySlopeRestriction W) 0 -
    infinityLeft W (infinitySlopeRestriction W) 0
  have hs := congrArg p (congrFun (infinityOutputCoordinates_scaled W) i)
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at hs
  have he := DFunLike.congr_fun (infinityProjective_inputs W t)
    (chartProductAdditionCoordinates W 1 1 i)
  have hi := congrArg (infinityProjectiveRestriction W t) (infinityAdditionChart_mul W i)
  simp only [map_mul] at hi
  change infinityIntersectionChart W t (coord W 1 i) *
    p (infinityOutputCoordinates W 1) = p (infinityOutputCoordinates W i) at hi
  change _ = (p d ^ 3 * p (infinityOutputCoordinates W 1)) *
    infinityIntersectionChart W t (coord W 1 i)
  calc
    _ = p d ^ 3 * p (infinityOutputCoordinates W i) := he.trans hs
    _ = _ := by rw [← hi]; ring

/-- The common scale is a unit because the polynomial output coordinate is a unit. -/
theorem infinityIntersectionScale_isUnit : IsUnit (infinityIntersectionScale W t) := by
  have hu := (additionOutput_isUnit W 1 1 t).map (infinityProjectivePolynomial W t)
  rw [infinityIntersection_scaled] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- The infinity output lies in the output-coordinate overlap required by the polynomial law. -/
theorem infinityIntersectionOutput_isUnit :
    IsUnit (infinityIntersectionChart W t (coord W 1 t)) := by
  have hu := (additionOutput_isUnit W 1 1 t).map (infinityProjectivePolynomial W t)
  rw [infinityIntersection_scaled] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- The restricted infinity map lifts through the actual integral output overlap. -/
def infinityIntersectionOutputLift : Overlap W 1 t →ₐ[R] InfinityProjectiveOverlap W t :=
  overlapLift W 1 t (infinityIntersectionChart W t) (infinityIntersectionOutput_isUnit W t)

/-- The output-overlap lift retains all normalized infinity coordinates. -/
@[simp] theorem infinityIntersectionOutputLift_coord (i : Fin 3) :
    infinityIntersectionOutputLift W t (overlapCoord W 1 t i) =
      infinityIntersectionChart W t (coord W 1 i) :=
  DFunLike.congr_fun (overlapLift_restriction W 1 t (infinityIntersectionChart W t)
    (infinityIntersectionOutput_isUnit W t)) (coord W 1 i)

/-- The integral output transition divides by precisely the selected infinity coordinate. -/
theorem infinityIntersectionOutputTransition_mul (i : Fin 3) :
    ((infinityIntersectionOutputLift W t).comp (transitionBase W 1 t)) (coord W t i) *
        infinityIntersectionChart W t (coord W 1 t) =
      infinityIntersectionChart W t (coord W 1 i) := by
  have hi := congrArg (infinityIntersectionOutputLift W t) (overlapInverse_mul W 1 t)
  rw [map_mul, map_one, infinityIntersectionOutputLift_coord] at hi
  change infinityIntersectionOutputLift W t (transitionBase W 1 t (coord W t i)) * _ = _
  rw [transitionBase_coord, map_mul, infinityIntersectionOutputLift_coord]
  linear_combination infinityIntersectionChart W t (coord W 1 i) * hi

/-- After the actual integral output transition the two addition algebra maps coincide. -/
theorem infinityIntersectionOutput_compatibility :
    (infinityProjectivePolynomial W t).comp (projectiveAdditionChart W 1 1 t) =
      (infinityIntersectionOutputLift W t).comp (transitionBase W 1 t) := by
  apply projectiveAdditionChart_comp_eq
  intro i
  rw [infinityIntersection_scaled, infinityIntersection_scaled]
  have hi := infinityIntersectionOutputTransition_mul W t i
  change _ * (infinityIntersectionScale W t *
    infinityIntersectionChart W t (coord W 1 t)) = _
  linear_combination infinityIntersectionScale W t * hi

end FLT.Mazur.WeierstrassIntegralChart
