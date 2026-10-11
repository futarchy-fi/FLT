/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothRestrictionCharts
public import FLT.Mazur.WeierstrassLeftSmoothFactorAddition
public import FLT.Mazur.WeierstrassSmoothFactorAddition

/-!
# Enlarged integral translation restricts to the original smooth group law

The actual inclusions of the smooth pair open and its categorical factor product
preserve both original inputs and the original addition morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original smooth pair open is contained in the left smooth input open. -/
def smoothProductToLeftSmooth :
    (smoothCurveProductOpen W).toScheme ⟶ (leftSmoothCurveProductOpen W).toScheme :=
  (integralCurveProduct W).homOfLE (show smoothCurveProductOpen W ≤
    leftSmoothCurveProductOpen W from inf_le_left)

/-- The enlarged-domain inclusion preserves the original global input pair. -/
@[reassoc] theorem smoothProductToLeftSmooth_inclusion :
    smoothProductToLeftSmooth W ≫ (leftSmoothCurveProductOpen W).ι =
      (smoothCurveProductOpen W).ι := Scheme.homOfLE_ι _ _

/-- Enlarged translation restricts exactly to the original smooth group addition. -/
@[reassoc] theorem smoothProductToLeftSmooth_addition :
    smoothProductToLeftSmooth W ≫ leftSmoothCurveAddition W =
      smoothCurveAddition W ≫ (integralSmoothOpen W).ι := by
  apply (smoothCurveProductCover W).hom_ext
  rintro ⟨b, c⟩
  rw [smoothCurveProductCover_addition_assoc]
  have h : ((smoothCurveProductCover W).f (b, c) ≫ smoothProductToLeftSmooth W) ≫
      (leftSmoothCurveProductOpen W).ι =
        smoothCurveProductCoverToChart W b c ≫ smoothProductChartInput W b c := by
    rw [Category.assoc, smoothProductToLeftSmooth_inclusion,
      smoothCurveProductCoverToChart_inputs]
  simpa only [Category.assoc] using leftSmoothCurveAddition_smoothChart W b c _ _ h

/-- The categorical smooth pair maps into the enlarged factor product using its actual inputs. -/
def smoothFactorsToLeftSmooth : smoothFactorProduct W ⟶ leftSmoothFactorProduct W :=
  smoothFactorsToProduct W ≫ smoothProductToLeftSmooth W ≫ leftSmoothProductToFactors W

/-- This factor inclusion retains the original projective input pair. -/
@[reassoc] theorem smoothFactorsToLeftSmooth_inclusion :
    smoothFactorsToLeftSmooth W ≫ leftSmoothFactorsInclusion W = smoothFactorsInclusion W := by
  simp only [smoothFactorsToLeftSmooth, Category.assoc,
    leftSmoothProductToFactors_inclusion, smoothProductToLeftSmooth_inclusion,
    smoothFactorsToProduct_inclusion]

/-- The enlarged factor inclusion retains the original smooth first point. -/
@[reassoc] theorem smoothFactorsToLeftSmooth_fst :
    smoothFactorsToLeftSmooth W ≫
        pullback.fst (integralSmoothStructure W) (integralCurveStructure W) =
      pullback.fst (integralSmoothStructure W) (integralSmoothStructure W) := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have h := congrArg (fun f => f ≫
    pullback.fst (integralCurveStructure W) (integralCurveStructure W))
      (smoothFactorsToLeftSmooth_inclusion W)
  simpa only [Category.assoc, leftSmoothFactorsInclusion, smoothFactorsInclusion,
    pullback.lift_fst] using h

/-- The enlarged factor inclusion retains the original second point in the whole cubic. -/
@[reassoc] theorem smoothFactorsToLeftSmooth_snd :
    smoothFactorsToLeftSmooth W ≫
        pullback.snd (integralSmoothStructure W) (integralCurveStructure W) =
      pullback.snd (integralSmoothStructure W) (integralSmoothStructure W) ≫
        (integralSmoothOpen W).ι := by
  have h := congrArg (fun f => f ≫
    pullback.snd (integralCurveStructure W) (integralCurveStructure W))
      (smoothFactorsToLeftSmooth_inclusion W)
  simpa only [Category.assoc, leftSmoothFactorsInclusion, smoothFactorsInclusion,
    pullback.lift_snd] using h

/-- Integral translation on smooth categorical pairs is the original group multiplication. -/
@[reassoc] theorem smoothFactorsToLeftSmooth_addition :
    smoothFactorsToLeftSmooth W ≫ leftSmoothFactorAddition W =
      smoothFactorAddition W ≫ (integralSmoothOpen W).ι := by
  simp only [smoothFactorsToLeftSmooth, Category.assoc, leftSmoothProductToFactors_addition,
    smoothProductToLeftSmooth_addition, smoothFactorAddition]

end FLT.Mazur.WeierstrassIntegralChart
