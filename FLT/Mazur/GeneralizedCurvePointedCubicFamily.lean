/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePointedCubicGroup
public import FLT.Mazur.WeierstrassGeneralizedSmoothComparison

/-!
# The full original generalized curve in a pointed cubic chart

The existing group comparison extends to the original full curve and action.
The target is the established generalized cubic pulled back along the original
canonical spectrum map. Projection recovers the complete supplied curve map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} [IsAffine S] (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]

/-- The established cubic DR object pulled back to the actual original affine base. -/
def pointedCubicFamily : GeneralizedEllipticCurve S :=
  (integralGeneralizedEllipticCurve W
    (WeierstrassCurve.IsElliptic.isUnit (W := W))).baseChange S.toSpecΓ

omit [IsAffine S] in
/-- The pulled-back nonsingular cubic's actual smooth inclusion is the identity. -/
theorem pointedCubicFamily_inclusion : (pointedCubicFamily W).inclusion = 𝟙 _ := by
  change ((integralGeneralizedEllipticCurve W
    (WeierstrassCurve.IsElliptic.isUnit (W := W))).baseChange S.toSpecΓ).inclusion = _
  rw [baseChange_inclusion, pullbackInclusion,
    integralGeneralizedEllipticCurve_inclusion]
  exact (Over.pullback S.toSpecΓ).map_id (integralCurveOver W)

variable (E : GeneralizedEllipticCurve S) [IsLocallyNoetherian S]
  (e : E.curve.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = E.curve.hom ≫ S.toSpecΓ)
  (hs : E.identitySection.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W)

/-- The original complete pointed cubic presentation is an isomorphism of full DR objects. -/
def pointedCubicFamilyIso : E ≅ pointedCubicFamily W := by
  let _ := smooth_of_pointedCubic E W e he
  let _ : IsIso (pointedCubicFamily W).inclusion := by
    rw [pointedCubicFamily_inclusion]
    infer_instance
  let _ := pointedCubicGroupIso_isMonHom E W e he hs
  exact isoOfSmoothGroup E (pointedCubicFamily W) (pointedCubicGroupIso E W e he)

/-- The full DR comparison retains exactly the original complete curve lift. -/
theorem pointedCubicFamilyIso_curve :
    (pointedCubicFamilyIso W E e he hs).hom.curve = pointedCubicBaseMap W E.curve e he := by
  let _ := smooth_of_pointedCubic E W e he
  apply (cancel_epi E.inclusion).mp
  rw [(pointedCubicFamilyIso W E e he hs).hom.inclusion, pointedCubicFamily_inclusion,
    Category.comp_id]
  rfl

/-- Projection of the full curve comparison is precisely the supplied original cubic map. -/
@[reassoc] theorem pointedCubicFamilyIso_curve_fst :
    (pointedCubicFamilyIso W E e he hs).hom.curve.left ≫
      pullback.fst (integralCurveStructure W) S.toSpecΓ = e.hom := by
  rw [pointedCubicFamilyIso_curve, pointedCubicBaseMap_fst]

end FLT.Mazur.GeneralizedEllipticCurve
