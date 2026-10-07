/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTransportedIntersection

/-!
# Input normalization on the full infinity and affine intersection

The original Y coordinates and transported affine coordinates are related by
units on the entire intersection. These identities retain the polynomial
base locus and provide the input inverses for the integral slope comparison.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i : AdditionChartIndex)

/-- The simultaneous input-chart overlap restricted to the full intersection. -/
def infinityTransportedOverlap :
    ProductOverlap W 1 1 2 2 →ₐ[R] InfinityTransportedIntersection W i :=
  (infinityTransportedAffine W i).comp (transportedAdditionOverlap W 1 1 i)

/-- The normalized affine inputs on the full intersection. -/
def infinityTransportedNormalized : AffineProduct W →ₐ[R] InfinityTransportedIntersection W i :=
  (infinityTransportedChart W i).comp (additionChartAlgRestriction W i)

/-- The overlap retains the original Y-chart inputs. -/
theorem infinityTransportedOverlap_original :
    (infinityTransportedOverlap W i).comp (productOverlapRestriction W 1 1 2 2) =
      infinityTransportedInput W i := infinityTransported_inputs W i

/-- The overlap retains the normalized affine inputs. -/
theorem infinityTransportedOverlap_normalized :
    (infinityTransportedOverlap W i).comp (productOverlapOther W 1 1 2 2) =
      infinityTransportedNormalized W i := by
  change (infinityTransportedAffine W i).comp
    ((transportedAdditionOverlap W 1 1 i).comp (productOverlapOther W 1 1 2 2)) = _
  rw [transportedAdditionRing_inputs]
  rfl

/-- Every left input coordinate has the explicit integral normalizing factor. -/
theorem infinityTransported_left_scaled (a : Fin 3) :
    infinityTransportedNormalized W i (productLeft W (coord W 2 a)) =
      infinityTransportedOverlap W i (productOverlapLeftScale W 1 1 2 2) *
        infinityLeft W (infinityTransportedInput W i) a := by
  have h := congrArg (infinityTransportedOverlap W i)
    (productOverlapOther_left W 1 1 2 2 a)
  rw [map_mul] at h
  have hn := DFunLike.congr_fun (infinityTransportedOverlap_normalized W i)
    (productLeft W (coord W 2 a))
  have ho := DFunLike.congr_fun (infinityTransportedOverlap_original W i)
    (chartProductLeft W 1 1 (coord W 1 a))
  exact hn.symm.trans (h.trans (congrArg (_ * ·) ho))

/-- Every right input coordinate has its own explicit integral normalizing factor. -/
theorem infinityTransported_right_scaled (a : Fin 3) :
    infinityTransportedNormalized W i (productRight W (coord W 2 a)) =
      infinityTransportedOverlap W i (productOverlapRightScale W 1 1 2 2) *
        infinityRight W (infinityTransportedInput W i) a := by
  have h := congrArg (infinityTransportedOverlap W i)
    (productOverlapOther_right W 1 1 2 2 a)
  rw [map_mul] at h
  have hn := DFunLike.congr_fun (infinityTransportedOverlap_normalized W i)
    (productRight W (coord W 2 a))
  have ho := DFunLike.congr_fun (infinityTransportedOverlap_original W i)
    (chartProductRight W 1 1 (coord W 1 a))
  exact hn.symm.trans (h.trans (congrArg (_ * ·) ho))

/-- Affine left Y is precisely the normalizing factor. -/
theorem infinityTransported_left_y :
    infinityTransportedNormalized W i (productY₁ W) =
      infinityTransportedOverlap W i (productOverlapLeftScale W 1 1 2 2) := by
  simpa only [productY₁, infinityLeft_one, mul_one] using infinityTransported_left_scaled W i 1

/-- Affine right Y is precisely the other normalizing factor. -/
theorem infinityTransported_right_y :
    infinityTransportedNormalized W i (productY₂ W) =
      infinityTransportedOverlap W i (productOverlapRightScale W 1 1 2 2) := by
  simpa only [productY₂, infinityRight_one, mul_one] using infinityTransported_right_scaled W i 1

/-- The original left Z coordinate is the inverse of normalized affine Y. -/
theorem infinityTransported_left_inverse :
    infinityLeft W (infinityTransportedInput W i) 2 *
      infinityTransportedNormalized W i (productY₁ W) = 1 := by
  have h := infinityTransported_left_scaled W i 2
  rw [coord_self, map_one, map_one, ← infinityTransported_left_y] at h
  exact (mul_comm _ _).trans h.symm

/-- The original right Z coordinate is the inverse of normalized affine Y. -/
theorem infinityTransported_right_inverse :
    infinityRight W (infinityTransportedInput W i) 2 *
      infinityTransportedNormalized W i (productY₂ W) = 1 := by
  have h := infinityTransported_right_scaled W i 2
  rw [coord_self, map_one, map_one, ← infinityTransported_right_y] at h
  exact (mul_comm _ _).trans h.symm

/-- Dividing affine left X by affine left Y recovers the original Y-chart X. -/
theorem infinityTransported_left_x :
    infinityTransportedNormalized W i (productX₁ W) *
        infinityLeft W (infinityTransportedInput W i) 2 =
      infinityLeft W (infinityTransportedInput W i) 0 := by
  have h := infinityTransported_left_scaled W i 0
  rw [← infinityTransported_left_y] at h
  change infinityTransportedNormalized W i (productX₁ W) = _ at h
  linear_combination infinityLeft W (infinityTransportedInput W i) 2 * h +
    infinityLeft W (infinityTransportedInput W i) 0 * infinityTransported_left_inverse W i

/-- Dividing affine right X by affine right Y recovers the original Y-chart X. -/
theorem infinityTransported_right_x :
    infinityTransportedNormalized W i (productX₂ W) *
        infinityRight W (infinityTransportedInput W i) 2 =
      infinityRight W (infinityTransportedInput W i) 0 := by
  have h := infinityTransported_right_scaled W i 0
  rw [← infinityTransported_right_y] at h
  change infinityTransportedNormalized W i (productX₂ W) = _ at h
  linear_combination infinityRight W (infinityTransportedInput W i) 2 * h +
    infinityRight W (infinityTransportedInput W i) 0 * infinityTransported_right_inverse W i

end FLT.Mazur.WeierstrassIntegralChart
