/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesCoordinates
public import FLT.Mazur.WeierstrassModificationXContractionOverlap

/-!
# The scale and horizontal Rees fraction overlaps

Localize the actual fraction charts at x/s and s/x. The existing equation
transition induces an isomorphism of these opens, retaining the original
cubic functions and sending the two overlap ratios to mutual inverses.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The x/s principal open in the actual scale fraction chart. -/
abbrev ScaleHorizontalOpen := Localization.Away (scaleHorizontal W s)

/-- The s/x principal open in the actual horizontal fraction chart. -/
abbrev HorizontalScaleOpen := Localization.Away (horizontalScale W s)

/-- The scale-chart comparison extends to its actual horizontal ratio open. -/
def scaleHorizontalOpenEquiv (hs : IsRegular s) :
    WeierstrassModificationX.DividedOpen W s b3 b4 b6 ≃ₐ[R] ScaleHorizontalOpen W s :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassDilatation.x W s b3 b4 b6))
    (T := Submonoid.powers (scaleHorizontal W s))
    (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs) (by
      rw [Submonoid.map_powers, scaleEquiv_x])

/-- The x-chart comparison extends to its actual scale ratio open. -/
def horizontalScaleOpenEquiv [IsDomain R] (hs : s ≠ 0) :
    WeierstrassModificationX.XOpen W s b3 b4 b6 ≃ₐ[R] HorizontalScaleOpen W s :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassModificationX.t W s b3 b4 b6))
    (T := Submonoid.powers (horizontalScale W s))
    (WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs) (by
      rw [Submonoid.map_powers, horizontalEquiv_t])

/-- The scale localization comparison retains every actual chart function. -/
@[simp] theorem scaleHorizontalOpenEquiv_base (hs : IsRegular s)
    (a : WeierstrassDilatation.Coordinate W s b3 b4 b6) :
    scaleHorizontalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs (algebraMap _ _ a) =
      algebraMap _ _ (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The horizontal localization comparison retains every actual chart function. -/
@[simp] theorem horizontalScaleOpenEquiv_base [IsDomain R] (hs : s ≠ 0)
    (a : WeierstrassModificationX.Coordinate W s b3 b4 b6) :
    horizontalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs (algebraMap _ _ a) =
      algebraMap _ _
        (WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The existing transition is an isomorphism of the actual original fraction opens. -/
def scaleHorizontalTransition [IsDomain R] (hs : s ≠ 0) :
    ScaleHorizontalOpen W s ≃ₐ[R] HorizontalScaleOpen W s :=
  ((scaleHorizontalOpenEquiv W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs)).symm.trans
    (WeierstrassModificationX.overlapEquiv W s b3 b4 b6)).trans
      (horizontalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs)

/-- The fraction transition is exactly the existing substitution on every scale function. -/
theorem scaleHorizontalTransition_base [IsDomain R] (hs : s ≠ 0)
    (a : WeierstrassDilatation.Coordinate W s b3 b4 b6) :
    scaleHorizontalTransition W s b3 b4 b6 h3 h4 h6 hs
      (algebraMap _ _ (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
        (IsRegular.of_ne_zero hs) a)) =
      horizontalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs
        (WeierstrassModificationX.dividedToXOpen W s b3 b4 b6 a) := by
  rw [← scaleHorizontalOpenEquiv_base]
  simp only [scaleHorizontalTransition, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  change horizontalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs
    (WeierstrassModificationX.overlapForward W s b3 b4 b6 (algebraMap _ _ a)) = _
  rw [WeierstrassModificationX.overlapForward_base]

/-- The transition sends x/s to the inverse of s/x in the actual fraction overlap. -/
theorem scaleHorizontalTransition_ratio [IsDomain R] (hs : s ≠ 0) :
    scaleHorizontalTransition W s b3 b4 b6 h3 h4 h6 hs
        (algebraMap _ (ScaleHorizontalOpen W s) (scaleHorizontal W s)) *
      algebraMap _ (HorizontalScaleOpen W s) (horizontalScale W s) = 1 := by
  have hd := congrArg (algebraMap (WeierstrassDilatation.scaleReesChart W s)
    (ScaleHorizontalOpen W s))
      (scaleEquiv_x W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs))
  have hx := congrArg (algebraMap (WeierstrassModificationX.horizontalReesChart W s)
    (HorizontalScaleOpen W s)) (horizontalEquiv_t W s b3 b4 b6 h3 h4 h6 hs)
  rw [← hd, scaleHorizontalTransition_base, ← hx, ← horizontalScaleOpenEquiv_base,
    ← map_mul]
  have hi : WeierstrassModificationX.dividedToXOpen W s b3 b4 b6
      (WeierstrassDilatation.x W s b3 b4 b6) *
      algebraMap _ (WeierstrassModificationX.XOpen W s b3 b4 b6)
        (WeierstrassModificationX.t W s b3 b4 b6) = 1 := by
    rw [WeierstrassModificationX.dividedToXOpen,
      WeierstrassModificationX.dividedOverlapMap_x,
      ← WeierstrassModificationX.xOpenUnit_val, Units.inv_mul]
  rw [hi, map_one]

end FLT.Mazur.WeierstrassModificationReesCoordinates
