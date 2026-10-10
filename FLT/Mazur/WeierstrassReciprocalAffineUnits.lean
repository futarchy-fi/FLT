/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionOutputFamilies

/-!
# Reciprocal addition with affine output

On a reciprocal chart the normalized output z-coordinate is a unit exactly
when the reciprocal slope is a unit. On this locus the corresponding ordinary
denominator is invertible too, including over nonreduced coefficient rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The reciprocal chart inverts the selected reversed denominator. -/
theorem reciprocalChartDenominator_isUnit (b : Bool) :
    IsUnit (additionChartAlgRestriction W (reciprocalIndex b)
      (if b then tangentNumerator W else verticalSecantDenominator W)) := by
  cases b
  · exact (IsLocalization.Away.algebraMap_isUnit (verticalSecantDenominator W)
      (S := RatioChart W (verticalSecantDenominator W))).map
        (reciprocalTargetRestriction W _ (verticalSecantSlope W))
  · exact (IsLocalization.Away.algebraMap_isUnit (tangentNumerator W)
      (S := RatioChart W (tangentNumerator W))).map
        (reciprocalTargetRestriction W _ (verticalTangentSlope W))

/-- The normalized z-coordinate is the unit normalization times the slope cube. -/
theorem reciprocalSpecialization_z (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) :
    f (reciprocalChartAddition W b (coord W 1 2)) =
      f (reciprocalChartInverse W b) * f (reciprocalChartSlope W b) ^ 3 := by
  rw [reciprocalChartAddition_coord]
  change f (reciprocalChartInverse W b * reciprocalChartSlope W b ^ 3) = _
  rw [map_mul, map_pow]

/-- Affine output is equivalent to an invertible reciprocal slope. -/
theorem reciprocalSpecialization_z_isUnit_iff (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) :
    IsUnit (f (reciprocalChartAddition W b (coord W 1 2))) ↔
      IsUnit (f (reciprocalChartSlope W b)) := by
  rw [reciprocalSpecialization_z, IsUnit.mul_iff, isUnit_pow_iff (by decide : 3 ≠ 0)]
  exact and_iff_right ((reciprocalChartInverse_isUnit W b).map f)

/-- With affine output, the same inputs lie in the corresponding ordinary domain. -/
theorem reciprocalSpecialization_ordinary_unit (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (hz : IsUnit (f (reciprocalChartAddition W b (coord W 1 2)))) :
    IsUnit (f (additionChartAlgRestriction W (reciprocalIndex b)
      (if b then tangentDenominator W else secantDenominator W))) := by
  have hm := (reciprocalSpecialization_z_isUnit_iff W b f).mp hz
  have hd := (reciprocalChartDenominator_isUnit W b).map f
  cases b with
  | false =>
    simpa only [ite_false, Bool.false_eq_true, ← reciprocalChartSlope_line, map_mul]
      using hm.mul hd
  | true =>
    simpa only [ite_true, ← reciprocalChartSlope_cubic, map_mul] using hm.mul hd

end FLT.Mazur.WeierstrassIntegralChart
