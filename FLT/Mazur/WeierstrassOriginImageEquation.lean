/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginImageCharts
public import FLT.Mazur.WeierstrassOriginDivisorPullback
public import FLT.Mazur.DivisorChartNumerator

/-!
# The origin equation on the actual image open

The original regular parameter is a section on an affine open of the cubic.
Its powers generate the intrinsic ideal powers there and give numerator
coordinates for sections of the original positive divisor line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.AffineImmersionSectionCoordinates

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original parameter, now a section on its image open in the original cubic. -/
def originImageParameter : Γ(integralCurve W, (originImageOpen W).1) :=
  (coordinates (originNeighborhoodInclusion W)).symm (originCoordinate W 0)

/-- The original image-open parameter is regular over arbitrary coefficient rings. -/
theorem originImageParameter_regular : IsRegular (originImageParameter W) :=
  flatRingHom_isRegular (coordinates (originNeighborhoodInclusion W)).symm.toRingHom
    (.of_bijective (coordinates (originNeighborhoodInclusion W)).symm.bijective)
    (originCoordinate_x_regular W)

/-- The actual intrinsic ideal power has its original parameter-power equation. -/
theorem originImageIdeal_power_equation (n : ℕ) :
    ((integralCurveZero W).ker ^ n).ideal (originImageOpen W) =
      Ideal.span {originImageParameter W ^ n} := by
  rw [ideal_comap, originIdealSheaf_power_neighborhood,
    originIdealSheaf_power_section_equation, Ideal.map_span, Set.image_singleton]
  have hp : (Scheme.ΓSpecIso (.of (OriginNeighborhood W))).hom.hom
      (originParameterSection W) = originCoordinate W 0 :=
    (originSectionRingEquiv W).symm_apply_apply _
  rw [map_pow, hp]
  have hm : Ideal.comap (coordinates (originNeighborhoodInclusion W)).toRingHom
      (Ideal.span {originCoordinate W 0 ^ n}) =
      Ideal.map (coordinates (originNeighborhoodInclusion W)).symm.toRingHom
        (Ideal.span {originCoordinate W 0 ^ n}) :=
    (Ideal.map_symm (coordinates (originNeighborhoodInclusion W))).symm
  rw [hm, Ideal.map_span, Set.image_singleton, map_pow]
  rfl

/-- Numerators of actual positive-line sections on the original image open. -/
def originImageNumerator (n : ℕ) :
    Γ(originDivisorLine W n, (originImageOpen W).1) ≃ₗ[Γ(integralCurve W,
      (originImageOpen W).1)] Γ(integralCurve W, (originImageOpen W).1) :=
  FCurve.divisorNumerator (originIdealSheaf_power_effectiveCartier W n)
    (originImageOpen W) (originImageParameter W ^ n)
    ((originImageParameter_regular W).pow n) (originImageIdeal_power_equation W n)

/-- The original coordinate of a numerator is an element of the original neighborhood ring. -/
def originImageNumeratorRing (n : ℕ)
    (s : Γ(originDivisorLine W n, (originImageOpen W).1)) : OriginNeighborhood W :=
  coordinates (originNeighborhoodInclusion W) (originImageNumerator W n s)

/-- Restricting the powered original equation gives the parameter used by the pole bound. -/
theorem originImageParameter_restrict (n : ℕ) :
    coordinates (originPunctureToCurve W)
      ((integralCurve W).presheaf.map (homOfLE (originOverlapOpen_le_image W)).op
        (originImageParameter W ^ n)) = originPunctureChart W (coord W 1 0) ^ n := by
  rw [originImageCoordinates_restrict, map_pow, map_pow]
  change algebraMap (OriginNeighborhood W) (OriginPuncture W)
    ((coordinates (originNeighborhoodInclusion W))
      ((coordinates (originNeighborhoodInclusion W)).symm (originCoordinate W 0))) ^ n = _
  rw [RingEquiv.apply_symm_apply, originPuncture_parameter]

end FLT.Mazur.WeierstrassIntegralChart
