/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesCoordinates
public import FLT.Mazur.WeierstrassModificationYHorizontalLocalization

/-!
# The horizontal and vertical Rees fraction overlaps

The existing y-chart substitution identifies the actual fraction opens at
y/x and x/y. Their original ratios become inverse units on the overlap.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The y/x principal open in the horizontal fraction chart. -/
abbrev HorizontalVerticalOpen := Localization.Away (horizontalVertical W s)

/-- The x/y principal open in the vertical fraction chart. -/
abbrev VerticalHorizontalOpen := Localization.Away (verticalHorizontal W s)

/-- The horizontal chart comparison extends to its vertical ratio open. -/
def horizontalVerticalOpenEquiv [IsDomain R] (hs : s ≠ 0) :
    WeierstrassModificationY.XVertical W s b3 b4 b6 ≃ₐ[R] HorizontalVerticalOpen W s :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassModificationX.v W s b3 b4 b6))
    (T := Submonoid.powers (horizontalVertical W s))
    (WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs) (by
      rw [Submonoid.map_powers, horizontalEquiv_v])

/-- The vertical chart comparison extends to its horizontal ratio open. -/
def verticalHorizontalOpenEquiv [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    WeierstrassModificationY.HorizontalOpen W s b3 b4 b6 ≃ₐ[R] VerticalHorizontalOpen W s :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers (WeierstrassModificationY.coord W s b3 b4 b6 1))
    (T := Submonoid.powers (verticalHorizontal W s))
    (WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs) (by
      rw [Submonoid.map_powers, verticalEquiv_u])

/-- The horizontal comparison retains every actual chart function. -/
@[simp] theorem horizontalVerticalOpenEquiv_base [IsDomain R] (hs : s ≠ 0)
    (a : WeierstrassModificationX.Coordinate W s b3 b4 b6) :
    horizontalVerticalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs (algebraMap _ _ a) =
      algebraMap _ _
        (WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The vertical comparison retains every actual chart function. -/
@[simp] theorem verticalHorizontalOpenEquiv_base [IsDomain R] [IsBezout R] (hs : s ≠ 0)
    (a : WeierstrassModificationY.Coordinate W s b3 b4 b6) :
    verticalHorizontalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs (algebraMap _ _ a) =
      algebraMap _ _
        (WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- The actual horizontal and vertical fraction opens are isomorphic. -/
def horizontalVerticalTransition [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    HorizontalVerticalOpen W s ≃ₐ[R] VerticalHorizontalOpen W s :=
  ((horizontalVerticalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs).symm.trans
    (WeierstrassModificationY.horizontalEquiv W s b3 b4 b6)).trans
      (verticalHorizontalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs)

/-- The fraction transition is the existing substitution on every horizontal chart function. -/
theorem horizontalVerticalTransition_base [IsDomain R] [IsBezout R] (hs : s ≠ 0)
    (a : WeierstrassModificationX.Coordinate W s b3 b4 b6) :
    horizontalVerticalTransition W s b3 b4 b6 h3 h4 h6 hs
      (algebraMap _ _
        (WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs a)) =
      verticalHorizontalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs
        (WeierstrassModificationY.toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
          (WeierstrassModificationY.horizontalUnit W s b3 b4 b6)
          (WeierstrassModificationY.horizontalUnit_val W s b3 b4 b6).symm a) := by
  rw [← horizontalVerticalOpenEquiv_base]
  simp only [horizontalVerticalTransition, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  change verticalHorizontalOpenEquiv W s b3 b4 b6 h3 h4 h6 hs
    (WeierstrassModificationY.horizontalForward W s b3 b4 b6 (algebraMap _ _ a)) = _
  rw [WeierstrassModificationY.horizontalForward_base]

/-- The two actual generator ratios are mutual inverses on this fraction overlap. -/
theorem horizontalVerticalTransition_ratio [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    horizontalVerticalTransition W s b3 b4 b6 h3 h4 h6 hs
        (algebraMap _ (HorizontalVerticalOpen W s) (horizontalVertical W s)) *
      algebraMap _ (VerticalHorizontalOpen W s) (verticalHorizontal W s) = 1 := by
  have hx := congrArg (algebraMap (WeierstrassModificationX.horizontalReesChart W s)
    (HorizontalVerticalOpen W s)) (horizontalEquiv_v W s b3 b4 b6 h3 h4 h6 hs)
  have hy := congrArg (algebraMap (WeierstrassModificationY.verticalReesChart W s)
    (VerticalHorizontalOpen W s)) (verticalEquiv_u W s b3 b4 b6 h3 h4 h6 hs)
  rw [← hx, horizontalVerticalTransition_base, WeierstrassModificationY.toX_v,
    ← hy, ← verticalHorizontalOpenEquiv_base,
    ← WeierstrassModificationY.horizontalUnit_val, ← map_mul, Units.inv_mul, map_one]

end FLT.Mazur.WeierstrassModificationReesCoordinates
