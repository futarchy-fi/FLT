/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAffineNormalization
public import FLT.Mazur.WeierstrassInfinityTransportedInputs
public import FLT.Mazur.WeierstrassAdditionSlopeFamilies

/-!
# Slope comparison on the full infinity and transported affine intersection

The regular infinity slope and both families of affine slopes satisfy the
integral intercept relation on the actual intersection, including the
polynomial base locus. In particular the intercept is a unit there.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i : AdditionChartIndex)

/-- Restriction of the infinity slope domain to the full intersection. -/
def infinityTransportedSlopeRestriction :
    InfinitySlopeOpen W →ₐ[R] InfinityTransportedIntersection W i :=
  (infinityTransportedInfinity W i).comp (infinityOutputRestriction W)

/-- The regular infinity slope on the actual intersection. -/
def infinityTransportedSlope : InfinityTransportedIntersection W i :=
  infinityTransportedSlopeRestriction W i (infinitySlope W)

/-- The infinity divided-difference denominator stays a unit on the full intersection. -/
theorem infinityTransportedDen_isUnit :
    IsUnit (infinityDen W (infinityTransportedInput W i)) := by
  have h := (infinityDen_isUnit W).map (infinityTransportedSlopeRestriction W i)
  simpa only [infinityDen_map, infinityTransportedSlopeRestriction,
    infinityTransportedInput, infinityAdditionRestriction, AlgHom.comp_assoc] using h

/-- The infinity slope keeps its defining relation on the full intersection. -/
theorem infinityTransportedSlope_relation :
    infinityTransportedSlope W i * infinityDen W (infinityTransportedInput W i) =
      infinityNum W (infinityTransportedInput W i) := by
  have h := congrArg (infinityTransportedSlopeRestriction W i) (infinitySlope_mul_den W)
  simpa only [map_mul, infinityDen_map, infinityNum_map, infinityTransportedSlope,
    infinityTransportedSlopeRestriction, infinityTransportedInput,
    infinityAdditionRestriction, AlgHom.comp_assoc] using h

/-- Every affine direction satisfying the two slope equations has the actual infinity slope. -/
theorem infinityTransported_intercept (p q : InfinityTransportedIntersection W i)
    (hl : q * (infinityTransportedNormalized W i (productX₁ W) -
      infinityTransportedNormalized W i (productX₂ W)) =
        p * (infinityTransportedNormalized W i (productY₁ W) -
          infinityTransportedNormalized W i (productY₂ W)))
    (hc : q * infinityTransportedNormalized W i (tangentDenominator W) =
      p * infinityTransportedNormalized W i (tangentNumerator W)) :
    infinityTransportedSlope W i *
      (p * infinityTransportedNormalized W i (productY₁ W) -
        q * infinityTransportedNormalized W i (productX₁ W)) = -q := by
  apply infinityAffineSlope_normalized (W.map (algebraMap R _))
    (infinityTransported_left_inverse W i) (infinityTransported_right_inverse W i)
    (productLeft_equation W (infinityTransportedNormalized W i)) hl
  · simpa only [map_tangentDenominator, map_tangentNumerator,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using hc
  · rw [infinityTransported_right_x]
    exact infinityTransportedDen_isUnit W i
  · rw [infinityTransported_left_x, infinityTransported_right_x]
    exact infinityTransportedSlope_relation W i

variable (b : Bool)

/-- Both ordinary affine slopes compare on the full intersection, including tangent inputs. -/
theorem infinityTransported_ordinary_slope :
    infinityTransportedSlope W (ordinaryIndex b) *
        (infinityTransportedNormalized W (ordinaryIndex b) (productY₁ W) -
          infinityTransportedChart W (ordinaryIndex b) (ordinaryChartSlope W b) *
            infinityTransportedNormalized W (ordinaryIndex b) (productX₁ W)) =
      -infinityTransportedChart W (ordinaryIndex b) (ordinaryChartSlope W b) := by
  have hl := congrArg (infinityTransportedChart W (ordinaryIndex b))
    (ordinaryChartSlope_line W b)
  have hc := congrArg (infinityTransportedChart W (ordinaryIndex b))
    (ordinaryChartSlope_cubic W b)
  have h := infinityTransported_intercept W (ordinaryIndex b) 1
    (infinityTransportedChart W (ordinaryIndex b) (ordinaryChartSlope W b))
    (by simpa only [map_mul, one_mul, infinityTransportedNormalized, AlgHom.comp_apply,
      map_secantDenominator, map_verticalSecantDenominator, map_sub] using hl)
    (by simpa only [map_mul, one_mul, infinityTransportedNormalized,
      AlgHom.comp_apply] using hc)
  simpa only [one_mul] using h

/-- Both reciprocal affine slopes compare on the full intersection, including vertical tangents. -/
theorem infinityTransported_reciprocal_slope :
    infinityTransportedSlope W (reciprocalIndex b) *
        (infinityTransportedChart W (reciprocalIndex b) (reciprocalChartSlope W b) *
            infinityTransportedNormalized W (reciprocalIndex b) (productY₁ W) -
          infinityTransportedNormalized W (reciprocalIndex b) (productX₁ W)) = -1 := by
  have hl := congrArg (infinityTransportedChart W (reciprocalIndex b))
    (reciprocalChartSlope_line W b)
  have hc := congrArg (infinityTransportedChart W (reciprocalIndex b))
    (reciprocalChartSlope_cubic W b)
  have h := infinityTransported_intercept W (reciprocalIndex b)
    (infinityTransportedChart W (reciprocalIndex b) (reciprocalChartSlope W b)) 1
    (by simpa only [map_mul, one_mul, infinityTransportedNormalized, AlgHom.comp_apply,
      map_secantDenominator, map_verticalSecantDenominator, map_sub] using hl.symm)
    (by simpa only [map_mul, one_mul, infinityTransportedNormalized,
      AlgHom.comp_apply] using hc.symm)
  simpa only [one_mul] using h

/-- The ordinary affine intercept is invertible without restricting away from the diagonal. -/
theorem infinityTransported_ordinary_intercept_isUnit :
    IsUnit (infinityTransportedNormalized W (ordinaryIndex b) (productY₁ W) -
      infinityTransportedChart W (ordinaryIndex b) (ordinaryChartSlope W b) *
        infinityTransportedNormalized W (ordinaryIndex b) (productX₁ W)) :=
  infinityAffineSlope_ordinary_intercept_isUnit
    (isUnit_of_mul_isUnit_right ((infinityTransported_left_inverse W (ordinaryIndex b)).symm ▸
      isUnit_one)) (infinityTransported_ordinary_slope W b)

/-- The reciprocal affine intercept is invertible on its full intersection as well. -/
theorem infinityTransported_reciprocal_intercept_isUnit :
    IsUnit (infinityTransportedChart W (reciprocalIndex b) (reciprocalChartSlope W b) *
        infinityTransportedNormalized W (reciprocalIndex b) (productY₁ W) -
      infinityTransportedNormalized W (reciprocalIndex b) (productX₁ W)) :=
  infinityAffineSlope_reciprocal_intercept_isUnit (infinityTransported_reciprocal_slope W b)

end FLT.Mazur.WeierstrassIntegralChart
