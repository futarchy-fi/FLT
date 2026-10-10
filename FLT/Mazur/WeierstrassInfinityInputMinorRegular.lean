/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineProductDifference
public import FLT.Mazur.WeierstrassProductOverlapFlat
public import FLT.Mazur.WeierstrassInfinityOutputRegularCriterion
public import FLT.Mazur.WeierstrassInputPolynomialScaling

/-!
# Regularity of the infinity input XZ minor

The simultaneous affine overlap is an injective restriction of the infinity
product. On this overlap the XZ minor differs from the affine X difference by
invertible normalization factors. Flatness of the affine overlap map supplies
regularity without imposing any condition on the coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The first normalizing factor cancels the first input Z coordinate. -/
theorem infinityProductOverlap_left_scale_z :
    productOverlapLeftScale W 1 1 2 2 *
      productOverlapRestriction W 1 1 2 2 (chartProductLeft W 1 1 (coord W 1 2)) = 1 := by
  have h := productOverlapOther_left W 1 1 2 2 2
  simpa only [coord_self, map_one] using h.symm

/-- The second normalizing factor cancels the second input Z coordinate. -/
theorem infinityProductOverlap_right_scale_z :
    productOverlapRightScale W 1 1 2 2 *
      productOverlapRestriction W 1 1 2 2 (chartProductRight W 1 1 (coord W 1 2)) = 1 := by
  have h := productOverlapOther_right W 1 1 2 2 2
  simpa only [coord_self, map_one] using h.symm

/-- Elementary normalization of the homogeneous input minor. -/
theorem normalized_x_difference {S : Type*} [CommRing S] (x y z w a b : S)
    (ha : a * z = 1) (hb : b * w = 1) :
    b * y - a * x = -(a * b) * (x * w - y * z) := by
  linear_combination -b * y * ha + a * x * hb

/-- The affine difference is a scalar multiple of the original XZ minor on the overlap. -/
theorem infinityInputXZMinor_overlap :
    productOverlapOther W 1 1 2 2
        (chartProductRight W 2 2 (coord W 2 0) - chartProductLeft W 2 2 (coord W 2 0)) =
      -(productOverlapLeftScale W 1 1 2 2 * productOverlapRightScale W 1 1 2 2) *
        productOverlapRestriction W 1 1 2 2 (infinityInputXZMinor W) := by
  rw [map_sub, productOverlapOther_left, productOverlapOther_right]
  simp only [infinityInputXZMinor, map_sub, map_mul]
  exact normalized_x_difference _ _ _ _ _ _
    (infinityProductOverlap_left_scale_z W) (infinityProductOverlap_right_scale_z W)

/-- The input XZ minor is regular in the original infinity chart product over every base. -/
theorem infinityInputXZMinor_regular : IsRegular (infinityInputXZMinor W) := by
  have h := flatRingHom_isRegular (productOverlapOther W 1 1 2 2).toRingHom
    (productOverlapOther_flat W 1 1 2 2) (affineProduct_x_right_sub_left_regular W)
  change IsRegular (productOverlapOther W 1 1 2 2
    (chartProductRight W 2 2 (coord W 2 0) - chartProductLeft W 2 2 (coord W 2 0))) at h
  rw [infinityInputXZMinor_overlap] at h
  exact chartRegular_of_injective (productOverlapRestriction W 1 1 2 2).toRingHom
    (infinityProductOverlapRestriction_injective W) h.of_mul_right

/-- The normalized output Z is regular on the actual infinity addition neighborhood. -/
theorem infinityAdditionChart_z_regular :
    IsRegular (infinityAdditionChart W (coord W 1 2)) :=
  infinityAdditionChart_z_regular_of_minor W (infinityInputXZMinor_regular W)

end FLT.Mazur.WeierstrassIntegralChart
