/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartRatio
public import FLT.Mazur.WeierstrassSuccessiveScaleReesChart

/-!
# The actual ratios on successive Rees charts

The deeper horizontal coordinate and the incidence coordinate are x/π and
π/x in the two fraction charts of the same preceding center.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

/-- The ratio x/π in the scale chart of the preceding center. -/
def scaleHorizontal : WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6 :=
  BlowupFractionChart.ratio I (algebraMap R B π) BX (Ideal.subset_span (by simp))

/-- The ratio π/x in the horizontal chart of the same preceding center. -/
def horizontalScale : WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6 :=
  BlowupFractionChart.ratio I BX (algebraMap R B π) (Ideal.subset_span (by simp))

/-- The deeper horizontal coordinate becomes the actual center ratio x/π. -/
theorem scaleEquiv_x (hπ : IsRegular π) :
    WeierstrassSuccessiveScale.scaleReesChartEquiv W s π b3 b4 b6 hπ
      (WeierstrassDilatation.x W (s * π) b3 b4 b6) =
        scaleHorizontal W s π b3 b4 b6 := by
  apply Subtype.ext
  change WeierstrassSuccessiveScale.toPreviousScaleOpen W s π b3 b4 b6
    (WeierstrassDilatation.x W (s * π) b3 b4 b6) = _
  rw [WeierstrassSuccessiveScale.toPreviousScaleOpen,
    WeierstrassSuccessiveScale.fractionMap_x]
  exact mul_comm _ _

/-- The actual incidence coordinate becomes the reciprocal center ratio π/x. -/
theorem horizontalEquiv_t [IsDomain R] (hπ : π ≠ 0) :
    WeierstrassSuccessiveX.horizontalReesChartEquiv W s π b3 b4 b6 hπ
      (WeierstrassSuccessiveX.coord W s π b3 b4 b6 0) =
        horizontalScale W s π b3 b4 b6 := by
  apply Subtype.ext
  change WeierstrassSuccessiveX.toPreviousHorizontalOpen W s π b3 b4 b6
    (WeierstrassSuccessiveX.coord W s π b3 b4 b6 0) = _
  rw [WeierstrassSuccessiveX.toPreviousHorizontalOpen_t,
    IsScalarTower.algebraMap_apply R B
      (WeierstrassSuccessiveX.PreviousHorizontalOpen W s π b3 b4 b6)]
  rfl

end FLT.Mazur.WeierstrassSuccessiveRees
