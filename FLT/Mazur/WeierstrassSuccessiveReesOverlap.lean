/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXSchemeOverlap

/-!
# The scale and horizontal Rees fraction overlaps

Localize the actual fraction charts at x/π and π/x. The existing equation
transition induces an isomorphism of these opens, retaining the preceding
divided functions and sending the two overlap ratios to mutual inverses.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The x/π principal open in the actual scale fraction chart. -/
abbrev ScaleHorizontalOpen := Localization.Away (scaleHorizontal W s π b3 b4 b6)

/-- The π/x principal open in the actual horizontal fraction chart. -/
abbrev HorizontalScaleOpen := Localization.Away (horizontalScale W s π b3 b4 b6)

/-- The scale-chart comparison extends to its actual horizontal ratio open. -/
def scaleHorizontalOpenEquiv (hπ : IsRegular π) :
    WeierstrassSuccessiveX.DividedOpen W s π b3 b4 b6 ≃ₐ[R] ScaleHorizontalOpen W s π b3 b4 b6 :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassDilatation.x W (s * π) b3 b4 b6))
    (T := Submonoid.powers (scaleHorizontal W s π b3 b4 b6))
    (WeierstrassSuccessiveScale.scaleReesChartEquiv W s π b3 b4 b6 hπ) (by
      rw [Submonoid.map_powers, scaleEquiv_x])

/-- The x-chart comparison extends to its actual scale ratio open. -/
def horizontalScaleOpenEquiv [IsDomain R] (hπ : π ≠ 0) :
    WeierstrassSuccessiveX.XOpen W s π b3 b4 b6 ≃ₐ[R] HorizontalScaleOpen W s π b3 b4 b6 :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassSuccessiveX.coord W s π b3 b4 b6 0))
    (T := Submonoid.powers (horizontalScale W s π b3 b4 b6))
    (WeierstrassSuccessiveX.horizontalReesChartEquiv W s π b3 b4 b6 hπ) (by
      rw [Submonoid.map_powers, horizontalEquiv_t])

/-- The scale localization comparison retains every actual chart function. -/
@[simp] theorem scaleHorizontalOpenEquiv_base (hπ : IsRegular π)
    (a : WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6) :
    scaleHorizontalOpenEquiv W s π b3 b4 b6 hπ (algebraMap _ _ a) =
      algebraMap _ _ (WeierstrassSuccessiveScale.scaleReesChartEquiv W s π b3 b4 b6 hπ a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The horizontal localization comparison retains every actual chart function. -/
@[simp] theorem horizontalScaleOpenEquiv_base [IsDomain R] (hπ : π ≠ 0)
    (a : WeierstrassSuccessiveX.Coordinate W s π b3 b4 b6) :
    horizontalScaleOpenEquiv W s π b3 b4 b6 hπ (algebraMap _ _ a) =
      algebraMap _ _
        (WeierstrassSuccessiveX.horizontalReesChartEquiv W s π b3 b4 b6 hπ a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The existing transition is an isomorphism of the actual original fraction opens. -/
def scaleHorizontalTransition [IsDomain R] (hπ : π ≠ 0) :
    ScaleHorizontalOpen W s π b3 b4 b6 ≃ₐ[R] HorizontalScaleOpen W s π b3 b4 b6 :=
  ((scaleHorizontalOpenEquiv W s π b3 b4 b6 (IsRegular.of_ne_zero hπ)).symm.trans
    (WeierstrassSuccessiveX.overlapEquiv W s π b3 b4 b6)).trans
      (horizontalScaleOpenEquiv W s π b3 b4 b6 hπ)

/-- The fraction transition is exactly the existing substitution on every scale function. -/
theorem scaleHorizontalTransition_base [IsDomain R] (hπ : π ≠ 0)
    (a : WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6) :
    scaleHorizontalTransition W s π b3 b4 b6 hπ
      (algebraMap _ _ (WeierstrassSuccessiveScale.scaleReesChartEquiv W s π b3 b4 b6
        (IsRegular.of_ne_zero hπ) a)) =
      horizontalScaleOpenEquiv W s π b3 b4 b6 hπ
        (WeierstrassSuccessiveX.dividedToXOpen W s π b3 b4 b6 a) := by
  rw [← scaleHorizontalOpenEquiv_base]
  simp only [scaleHorizontalTransition, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  change horizontalScaleOpenEquiv W s π b3 b4 b6 hπ
    (WeierstrassSuccessiveX.overlapForward W s π b3 b4 b6 (algebraMap _ _ a)) = _
  rw [WeierstrassSuccessiveX.overlapForward_base]

/-- The transition sends x/π to the inverse of π/x in the actual fraction overlap. -/
theorem scaleHorizontalTransition_ratio [IsDomain R] (hπ : π ≠ 0) :
    scaleHorizontalTransition W s π b3 b4 b6 hπ
        (algebraMap _ (ScaleHorizontalOpen W s π b3 b4 b6) (scaleHorizontal W s π b3 b4 b6)) *
      algebraMap _ (HorizontalScaleOpen W s π b3 b4 b6) (horizontalScale W s π b3 b4 b6) = 1 := by
  have hd := congrArg (algebraMap (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)
    (ScaleHorizontalOpen W s π b3 b4 b6))
      (scaleEquiv_x W s π b3 b4 b6 (IsRegular.of_ne_zero hπ))
  have hx := congrArg (algebraMap (WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6)
    (HorizontalScaleOpen W s π b3 b4 b6)) (horizontalEquiv_t W s π b3 b4 b6 hπ)
  rw [← hd, scaleHorizontalTransition_base, ← hx, ← horizontalScaleOpenEquiv_base,
    ← map_mul]
  have hi : WeierstrassSuccessiveX.dividedToXOpen W s π b3 b4 b6
      (WeierstrassDilatation.x W (s * π) b3 b4 b6) *
      algebraMap _ (WeierstrassSuccessiveX.XOpen W s π b3 b4 b6)
        (WeierstrassSuccessiveX.coord W s π b3 b4 b6 0) = 1 := by
    rw [WeierstrassSuccessiveX.dividedToXOpen,
      WeierstrassSuccessiveX.dividedOverlapMap_x,
      ← WeierstrassSuccessiveX.xOpenUnit_val, Units.inv_mul]
  rw [hi, map_one]

end FLT.Mazur.WeierstrassSuccessiveRees
