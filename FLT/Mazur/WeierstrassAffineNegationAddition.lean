/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNegationPairSections

/-!
# Reciprocal addition sends an affine point and its negation to zero

On either reciprocal addition domain the defining slope specializes to zero
along the actual point-negation pair. The regular addition map consequently
specializes to the original infinity evaluation, over arbitrary algebras.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Each reciprocal slope denominator stays invertible after the output localization. -/
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

/-- On a point-negation pair, the reciprocal secant or tangent slope is zero. -/
theorem reciprocalChartSlope_negation (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) (g : Coordinate W 2 →ₐ[R] S)
    (h : f.comp (additionChartAlgRestriction W (reciprocalIndex b)) =
      g.comp (affineNegationPair W)) : f (reciprocalChartSlope W b) = 0 := by
  have hu := (reciprocalChartDenominator_isUnit W b).map f
  have he (a) : f (additionChartAlgRestriction W (reciprocalIndex b) a) =
      g (affineNegationPair W a) := DFunLike.congr_fun h a
  cases b
  · have hl := congrArg f (reciprocalChartSlope_line W false)
    rw [map_mul, he (secantDenominator W), affineNegationPair_secantDenominator, map_zero]
      at hl
    apply hu.mul_left_inj.mp
    simpa only [Bool.false_eq_true, ↓reduceIte, zero_mul] using hl
  · have hl := congrArg f (reciprocalChartSlope_cubic W true)
    rw [map_mul, he (tangentDenominator W), affineNegationPair_tangentDenominator, map_zero]
      at hl
    apply hu.mul_left_inj.mp
    simpa only [↓reduceIte, zero_mul] using hl

/-- A zero reciprocal slope makes the full normalized chart map the infinity evaluation. -/
theorem reciprocalChartAddition_zero (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (hm : f (reciprocalChartSlope W b) = 0) :
    f.comp (reciprocalChartAddition W b) = chartInfinityEvaluation W := by
  apply hom_ext
  intro i
  rw [chartInfinityEvaluation_coord]
  cases b
  · change f (verticalSecantAddition W (coord W 1 i)) = _
    exact reciprocalAddition_at_zero W _ _ _ _ f hm i
  · change f (verticalTangentAddition W (coord W 1 i)) = _
    exact reciprocalAddition_at_zero W _ _ _ _ f hm i

/-- Both reciprocal addition maps send the actual affine point-negation pair to zero. -/
theorem reciprocalChartAddition_negation (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) (g : Coordinate W 2 →ₐ[R] S)
    (h : f.comp (additionChartAlgRestriction W (reciprocalIndex b)) =
      g.comp (affineNegationPair W)) :
    f.comp (reciprocalChartAddition W b) = chartInfinityEvaluation W :=
  reciprocalChartAddition_zero W b f (reciprocalChartSlope_negation W b f g h)

end FLT.Mazur.WeierstrassIntegralChart
