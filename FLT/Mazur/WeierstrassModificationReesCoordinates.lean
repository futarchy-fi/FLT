/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartRatio
public import FLT.Mazur.WeierstrassModificationXReesChart
public import FLT.Mazur.WeierstrassModificationYReesChart

/-!
# Original generator ratios under the chart comparisons

The overlap coordinates become exactly x/s, s/x, y/x, s/y and x/y in the
fraction charts of the same original center. This specifies the principal
opens independently of the equation presentations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)

local notation "A" => WeierstrassIntegralChart.Coordinate W 2
local notation "I" => WeierstrassDilatation.modificationCenter W s
local notation "ox" => WeierstrassIntegralChart.coord W 2 0
local notation "oy" => WeierstrassIntegralChart.coord W 2 1

/-- The actual horizontal-to-scale ratio in the scale fraction algebra. -/
def scaleHorizontal : WeierstrassDilatation.scaleReesChart W s :=
  BlowupFractionChart.ratio I (algebraMap R A s) ox
    (Ideal.subset_span (by simp))

/-- The actual scale-to-horizontal ratio in the horizontal fraction algebra. -/
def horizontalScale : WeierstrassModificationX.horizontalReesChart W s :=
  BlowupFractionChart.ratio I ox (algebraMap R A s) (Ideal.subset_span (by simp))

/-- The actual vertical-to-horizontal ratio in the horizontal fraction algebra. -/
def horizontalVertical : WeierstrassModificationX.horizontalReesChart W s :=
  BlowupFractionChart.ratio I ox oy (Ideal.subset_span (by simp))

/-- The actual scale-to-vertical ratio in the vertical fraction algebra. -/
def verticalScale : WeierstrassModificationY.verticalReesChart W s :=
  BlowupFractionChart.ratio I oy (algebraMap R A s) (Ideal.subset_span (by simp))

/-- The actual horizontal-to-vertical ratio in the vertical fraction algebra. -/
def verticalHorizontal : WeierstrassModificationY.verticalReesChart W s :=
  BlowupFractionChart.ratio I oy ox (Ideal.subset_span (by simp))

variable (b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The divided overlap coordinate is exactly the original ratio x/s. -/
theorem scaleEquiv_x (hs : IsRegular s) :
    WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassDilatation.x W s b3 b4 b6) = scaleHorizontal W s := by
  apply Subtype.ext
  change WeierstrassDilatation.toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6
    (WeierstrassDilatation.x W s b3 b4 b6) = _
  rw [WeierstrassDilatation.toOriginalScaleOpen, WeierstrassDilatation.fractionMap_x]
  exact mul_comm _ _

/-- The x-chart incidence coordinate is exactly the original ratio s/x. -/
theorem horizontalEquiv_t [IsDomain R] (hs : s ≠ 0) :
    WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationX.t W s b3 b4 b6) = horizontalScale W s := by
  apply Subtype.ext
  change WeierstrassModificationX.toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6
    (WeierstrassModificationX.t W s b3 b4 b6) = _
  rw [WeierstrassModificationX.toOriginalHorizontalOpen,
    WeierstrassModificationX.fractionMap_t]
  rw [IsScalarTower.algebraMap_apply R A (WeierstrassModificationX.OriginalHorizontalOpen W)]
  exact mul_comm _ _

/-- The x-chart slope is exactly the original ratio y/x. -/
theorem horizontalEquiv_v [IsDomain R] (hs : s ≠ 0) :
    WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationX.v W s b3 b4 b6) = horizontalVertical W s := by
  apply Subtype.ext
  change WeierstrassModificationX.toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6
    (WeierstrassModificationX.v W s b3 b4 b6) = _
  rw [WeierstrassModificationX.toOriginalHorizontalOpen,
    WeierstrassModificationX.fractionMap_v]
  exact mul_comm _ _

/-- The y-chart scale coordinate is exactly the original ratio s/y. -/
theorem verticalEquiv_r [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationY.coord W s b3 b4 b6 0) = verticalScale W s := by
  apply Subtype.ext
  change WeierstrassModificationY.toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6
    (WeierstrassModificationY.coord W s b3 b4 b6 0) = _
  rw [WeierstrassModificationY.toOriginalVerticalOpen, WeierstrassModificationY.fractionMap_coord]
  change IsLocalization.Away.invSelf oy *
    algebraMap R (WeierstrassModificationY.OriginalVerticalOpen W) s = _
  rw [IsScalarTower.algebraMap_apply R A (WeierstrassModificationY.OriginalVerticalOpen W)]
  exact mul_comm _ _

/-- The y-chart horizontal coordinate is exactly the original ratio x/y. -/
theorem verticalEquiv_u [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationY.coord W s b3 b4 b6 1) = verticalHorizontal W s := by
  apply Subtype.ext
  change WeierstrassModificationY.toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6
    (WeierstrassModificationY.coord W s b3 b4 b6 1) = _
  rw [WeierstrassModificationY.toOriginalVerticalOpen, WeierstrassModificationY.fractionMap_coord]
  exact mul_comm _ _

end FLT.Mazur.WeierstrassModificationReesCoordinates
