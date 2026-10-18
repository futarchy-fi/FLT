/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteGeometricRotations
public import FLT.Mazur.OneGonSmoothingRelativeGroup
public import FLT.Mazur.GeneralizedEllipticCurve

/-!
# The actual complete one-gon as a generalized elliptic curve

The original complete cubic, its actual smooth group, and the constructed whole
action satisfy the classified family, action, and geometric rotation requirements.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] family_lfp
variable (K : Type) [Field K]
local notation "t" => (PowerSeries.X : PowerSeries K)

/-- The complete one-gon with its original smooth group and whole action. -/
def completeGeneralizedCurve : GeneralizedEllipticCurve (Spec (.of (PowerSeries K))) where
  curve := family (t)
  family := complete_classifiedGenusOneFamily K
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
  rotations := completeWholeAction_geometricRotations K

/-- The bundled generalized curve retains the original complete cubic. -/
theorem completeGeneralizedCurve_curve :
    (completeGeneralizedCurve K).curve = family (t) := rfl

/-- Its group is precisely the original complete smooth group. -/
theorem completeGeneralizedCurve_group :
    (completeGeneralizedCurve K).group = (relativeGroup (t)).X := rfl

/-- Its inclusion is precisely the original smooth-open inclusion. -/
theorem completeGeneralizedCurve_inclusion :
    (completeGeneralizedCurve K).inclusion = relativeGroupInclusion (t) := by
  change 𝟙 _ ≫ curveSmoothInclusion (family (t)) = _
  rw [Category.id_comp]
  rfl

/-- Its entire action is the constructed original smooth-by-whole addition. -/
theorem completeGeneralizedCurve_action :
    (completeGeneralizedCurve K).act = integralSmoothWholeAction (equation (t)) := rfl

/-- The generalized identity is the original marked section of the cubic. -/
theorem completeGeneralizedCurve_identity :
    (completeGeneralizedCurve K).identitySection.left = marking (t) := by
  change (η[(relativeGroup (t)).X] ≫ (completeGeneralizedCurve K).inclusion).left = _
  rw [completeGeneralizedCurve_inclusion]
  exact relativeGroup_identity (t)

end FLT.Mazur.OneGonSmoothing
