/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonRotations
public import FLT.Mazur.OneGonSmoothingRelativeGroup
public import FLT.Mazur.GeneralizedEllipticCurve

/-!
# Actual arithmetic one-gon generalized elliptic curves

The original cubic, smooth group, whole action, and geometric rotations assemble
over every arithmetic coefficient ring with invertible complementary discriminant
factor. In particular the construction works over the mixed-characteristic base Z[[t]].
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing WeierstrassIntegralChart ArithmeticOneGonRotations
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] family_lfp
variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))

/-- The arithmetic one-gon with its original smooth group and whole action. -/
def curve : GeneralizedEllipticCurve (Spec (.of R)) where
  curve := family (t)
  family := ArithmeticOneGonFamily.classifiedGenusOneFamily t ht
  group := (relativeGroup (t)).X
  smoothIso := Iso.refl _
  act := integralSmoothWholeAction (equation (t))
  unit_act := integralSmoothWholeAction_unit (equation (t))
  assoc_act := integralSmoothWholeAction_assoc (equation (t))
  restriction := by
    have hi : curveSmoothInclusion (family (t)) =
        integralSmoothWholeInclusion (equation (t)) := rfl
    simp only [Iso.refl_hom, Category.id_comp, hi]
    exact integralSmoothWholeAction_restriction (equation (t))
  rotations := wholeAction_geometricRotations t ht

/-- The bundled generalized curve retains the original arithmetic cubic. -/
theorem curve_curve :
    (curve t ht).curve = family (t) := rfl

/-- Its group is precisely the original arithmetic smooth group. -/
theorem curve_group :
    (curve t ht).group = (relativeGroup (t)).X := rfl

/-- Its inclusion is precisely the original smooth-open inclusion. -/
theorem curve_inclusion :
    (curve t ht).inclusion = relativeGroupInclusion (t) := by
  change 𝟙 _ ≫ curveSmoothInclusion (family (t)) = _
  rw [Category.id_comp]
  rfl

/-- Its entire action is the constructed original smooth-by-whole addition. -/
theorem curve_action :
    (curve t ht).act = integralSmoothWholeAction (equation (t)) := rfl

/-- The generalized identity is the original marked section of the cubic. -/
theorem curve_identity :
    (curve t ht).identitySection.left = marking (t) := by
  change (η[(relativeGroup (t)).X] ≫ (curve t ht).inclusion).left = _
  rw [curve_inclusion]
  exact relativeGroup_identity (t)

/-- A mixed-characteristic degeneration with the original integral power-series parameter. -/
def integralPowerSeriesCurve : GeneralizedEllipticCurve (Spec (.of (PowerSeries ℤ))) :=
  curve PowerSeries.X powerSeries_discriminant_factor_unit

/-- The integral degeneration retains the exact cubic over the original arithmetic base. -/
theorem integralPowerSeriesCurve_curve :
    integralPowerSeriesCurve.curve = family (PowerSeries.X : PowerSeries ℤ) := rfl

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
