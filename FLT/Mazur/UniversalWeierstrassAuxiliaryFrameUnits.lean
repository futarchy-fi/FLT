/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateInverse
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateUnits
public import FLT.Mazur.WeierstrassFrameNormalization

/-!
# The original auxiliary frame determines actual global units

The order-four label (1,0), its inverse, and (0,1) supply the horizontal
and vertical units used for canonical normalization. Taking these units
on the original auxiliary section ring retains arbitrary pullback functoriality.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.UniversalWeierstrass

/-- The first primitive label of the fixed auxiliary basis. -/
def frameLabelFirst : Labels 4 := Multiplicative.ofAdd (1, 0)

/-- The second primitive label supplies the horizontal frame separation. -/
def frameLabelThird : Labels 4 := Multiplicative.ofAdd (0, 1)

/-- The first label is not the identity. -/
theorem frameLabelFirst_ne : frameLabelFirst ≠ 1 := by decide

/-- The third label is not the identity. -/
theorem frameLabelThird_ne : frameLabelThird ≠ 1 := by decide

/-- The horizontal difference is a unit on the actual auxiliary scheme. -/
def auxiliaryFrameHorizontalUnit : AuxiliarySectionRingˣ :=
  (auxiliaryCoordinate_x_sub_isUnit frameLabelFirst frameLabelThird
    frameLabelFirst_ne frameLabelThird_ne (by decide) (by decide)).unit

/-- The vertical difference from the inverse label is an actual global unit. -/
def auxiliaryFrameVerticalUnit : AuxiliarySectionRingˣ :=
  (auxiliaryCoordinate_y_sub_neg_isUnit frameLabelFirst frameLabelFirst_ne (by decide)).unit

/-- The horizontal unit retains its original coordinate expression. -/
theorem auxiliaryFrameHorizontalUnit_val :
    (auxiliaryFrameHorizontalUnit : AuxiliarySectionRing) =
      auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0 -
        auxiliaryCoordinate frameLabelThird frameLabelThird_ne 0 := IsUnit.unit_spec _

/-- The vertical unit retains the original inverse-label coordinate expression. -/
theorem auxiliaryFrameVerticalUnit_val :
    (auxiliaryFrameVerticalUnit : AuxiliarySectionRing) =
      auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 1 -
        auxiliaryCoordinate frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne) 1 := by
  rw [auxiliaryCoordinate_inverse_y frameLabelFirst frameLabelFirst_ne]
  exact IsUnit.unit_spec _

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The admissible normalization is constructed from the actual global frame. -/
def auxiliaryFrameChange : WeierstrassCurve.VariableChange R :=
  WeierstrassFrameNormalization.change
    (g (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0))
    (g (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 1))
    (g (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 1))
    (Units.map g auxiliaryFrameHorizontalUnit) (Units.map g auxiliaryFrameVerticalUnit)

/-- The normalized frame separation is an actual unit over every pullback ring. -/
def auxiliaryFrameSeparation : Rˣ :=
  WeierstrassFrameNormalization.separation
    (Units.map g auxiliaryFrameHorizontalUnit) (Units.map g auxiliaryFrameVerticalUnit)

end FLT.Mazur.UniversalWeierstrass
