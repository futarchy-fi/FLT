/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesCoordinates
public import FLT.Mazur.WeierstrassModificationYScaleLocalization

/-!
# The scale and vertical Rees fraction overlaps

The existing y-chart substitution identifies the actual fraction opens at
y/s and s/y. Their original ratios become inverse units on the overlap.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The original y/s generator ratio in the scale fraction chart. -/
def scaleVertical : WeierstrassDilatation.scaleReesChart W s :=
  BlowupFractionChart.ratio (WeierstrassDilatation.modificationCenter W s)
    (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s)
    (WeierstrassIntegralChart.coord W 2 1) (Ideal.subset_span (by simp))

/-- The divided vertical coordinate is exactly the original ratio y/s. -/
theorem scaleEquiv_y [IsDomain R] (hs : s ≠ 0) :
    WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
      (IsRegular.of_ne_zero hs) (WeierstrassDilatation.y W s b3 b4 b6) =
        scaleVertical W s := by
  apply Subtype.ext
  change WeierstrassDilatation.toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6
    (WeierstrassDilatation.y W s b3 b4 b6) = _
  rw [WeierstrassDilatation.toOriginalScaleOpen, WeierstrassDilatation.fractionMap_y]
  exact mul_comm _ _

/-- The y/s principal open in the scale fraction chart. -/
abbrev ScaleVerticalOpen := Localization.Away (scaleVertical W s)

/-- The s/y principal open in the vertical fraction chart. -/
abbrev VerticalScaleOpen := Localization.Away (verticalScale W s)

/-- The scale chart comparison extends to its vertical ratio open. -/
def scaleVerticalOpenEquiv [IsDomain R] (hs : s ≠ 0) :
    WeierstrassModificationY.DividedVertical W s b3 b4 b6 ≃ₐ[R] ScaleVerticalOpen W s :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassDilatation.y W s b3 b4 b6))
    (T := Submonoid.powers (scaleVertical W s))
    (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
      (IsRegular.of_ne_zero hs)) (by
      rw [Submonoid.map_powers, scaleEquiv_y W s b3 b4 b6 h3 h4 h6 hs])

/-- The vertical chart comparison extends to its scale ratio open. -/
def verticalScaleOpenEquiv [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    WeierstrassModificationY.ScaleOpen W s b3 b4 b6 ≃ₐ[R] VerticalScaleOpen W s :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassModificationY.coord W s b3 b4 b6 0))
    (T := Submonoid.powers (verticalScale W s))
    (WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs) (by
      rw [Submonoid.map_powers, verticalEquiv_r])

/-- The scale comparison retains every actual chart function. -/
@[simp] theorem scaleVerticalOpenEquiv_base [IsDomain R] (hs : s ≠ 0)
    (a : WeierstrassDilatation.Coordinate W s b3 b4 b6) :
    scaleVerticalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs (algebraMap _ _ a) =
      algebraMap _ _
        (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
          (IsRegular.of_ne_zero hs) a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The vertical comparison retains every actual chart function. -/
@[simp] theorem verticalScaleOpenEquiv_base [IsDomain R] [IsBezout R] (hs : s ≠ 0)
    (a : WeierstrassModificationY.Coordinate W s b3 b4 b6) :
    verticalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs (algebraMap _ _ a) =
      algebraMap _ _
        (WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The actual scale and vertical fraction opens are isomorphic. -/
def scaleVerticalTransition [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    ScaleVerticalOpen W s ≃ₐ[R] VerticalScaleOpen W s :=
  ((scaleVerticalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs).symm.trans
    (WeierstrassModificationY.scaleEquiv W s b3 b4 b6)).trans
      (verticalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs)

/-- The fraction transition is the existing substitution on every scale chart function. -/
theorem scaleVerticalTransition_base [IsDomain R] [IsBezout R] (hs : s ≠ 0)
    (a : WeierstrassDilatation.Coordinate W s b3 b4 b6) :
    scaleVerticalTransition W s b3 b4 b6 h3 h4 h6 hs
      (algebraMap _ _
        (WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
          (IsRegular.of_ne_zero hs) a)) =
      verticalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs
        (WeierstrassModificationY.toDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
          (WeierstrassModificationY.scaleUnit W s b3 b4 b6)
          (WeierstrassModificationY.scaleUnit_val W s b3 b4 b6).symm a) := by
  rw [← scaleVerticalOpenEquiv_base W s b3 b4 b6 h3 h4 h6 hs]
  simp only [scaleVerticalTransition, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  change verticalScaleOpenEquiv W s b3 b4 b6 h3 h4 h6 hs
    (WeierstrassModificationY.scaleForward W s b3 b4 b6 (algebraMap _ _ a)) = _
  rw [WeierstrassModificationY.scaleForward_base]

/-- The two actual generator ratios are mutual inverses on this fraction overlap. -/
theorem scaleVerticalTransition_ratio [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    scaleVerticalTransition W s b3 b4 b6 h3 h4 h6 hs
        (algebraMap _ (ScaleVerticalOpen W s) (scaleVertical W s)) *
      algebraMap _ (VerticalScaleOpen W s) (verticalScale W s) = 1 := by
  have hd := congrArg (algebraMap (WeierstrassDilatation.scaleReesChart W s)
    (ScaleVerticalOpen W s)) (scaleEquiv_y W s b3 b4 b6 h3 h4 h6 hs)
  have hy := congrArg (algebraMap (WeierstrassModificationY.verticalReesChart W s)
    (VerticalScaleOpen W s)) (verticalEquiv_r W s b3 b4 b6 h3 h4 h6 hs)
  rw [← hd, scaleVerticalTransition_base, WeierstrassModificationY.toDivided_y,
    ← hy, ← verticalScaleOpenEquiv_base,
    ← WeierstrassModificationY.scaleUnit_val, ← map_mul, Units.inv_mul, map_one]

end FLT.Mazur.WeierstrassModificationReesCoordinates
