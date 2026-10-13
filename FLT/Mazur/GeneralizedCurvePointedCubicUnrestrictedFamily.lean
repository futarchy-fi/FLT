/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePointedCubicFamily
public import FLT.Mazur.PointedCubicUnrestrictedGroup

/-!
# Complete pointed cubic families over unrestricted affine bases

A supplied original pointed cubic presentation determines an isomorphism of
full generalized elliptic curves, including actions, over any affine base.
The group law is proved compatible by unrestricted proper smooth rigidity.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} [IsAffine S] (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]

variable (E : GeneralizedEllipticCurve S)
  (e : E.curve.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = E.curve.hom ≫ S.toSpecΓ)
  (hs : E.identitySection.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W)

/-- The original complete pointed cubic presentation is an isomorphism of full DR objects. -/
def pointedCubicFamilyIsoUnrestricted : E ≅ pointedCubicFamily W := by
  let _ := smooth_of_pointedCubic E W e he
  let _ : IsIso (pointedCubicFamily W).inclusion := by
    rw [pointedCubicFamily_inclusion]
    infer_instance
  let _ := pointedCubicGroupIso_isMonHom_unrestricted E W e he hs
  exact isoOfSmoothGroup E (pointedCubicFamily W) (pointedCubicGroupIso E W e he)

/-- The full DR comparison retains exactly the original complete curve lift. -/
theorem pointedCubicFamilyIsoUnrestricted_curve :
    (pointedCubicFamilyIsoUnrestricted W E e he hs).hom.curve =
      pointedCubicBaseMap W E.curve e he := by
  let _ := smooth_of_pointedCubic E W e he
  apply (cancel_epi E.inclusion).mp
  rw [(pointedCubicFamilyIsoUnrestricted W E e he hs).hom.inclusion,
    pointedCubicFamily_inclusion,
    Category.comp_id]
  rfl

/-- Projection of the full curve comparison is precisely the supplied original cubic map. -/
@[reassoc] theorem pointedCubicFamilyIsoUnrestricted_curve_fst :
    (pointedCubicFamilyIsoUnrestricted W E e he hs).hom.curve.left ≫
      pullback.fst (integralCurveStructure W) S.toSpecΓ = e.hom := by
  rw [pointedCubicFamilyIsoUnrestricted_curve, pointedCubicBaseMap_fst]

end FLT.Mazur.GeneralizedEllipticCurve
