/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePointedCubicGroup
public import FLT.Mazur.ProperSmoothRelativePointedGroupHom

/-!
# The group law of a pointed cubic presentation over arbitrary bases

The actual pointed comparison preserves the established cubic law without
Noetherianity. This removes the group-law restriction independently of the
remaining construction of a cubic presentation for each original family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsAffine S] (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (e : G.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = G.hom ≫ S.toSpecΓ)
/-- The original pulled cubic carries its established commutative group structure. -/
local instance unrestrictedPointedCubicCommGrp : CommGrpObj (pointedCubicBase W) :=
  pointedCubicBaseCommGrp W

/-- Pointed cubic lifts preserve the original group law over every affine base. -/
theorem pointedCubicBaseMap_isMonHom_unrestricted
    (hs : (η[G]).left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W) :
    IsMonHom (pointedCubicBaseMap W G e he) := by
  let _ : IsSeparated (pointedCubicBase W).hom :=
    inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))
  let _ : LocallyOfFiniteType (pointedCubicBase W).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (integralCurveStructure W) S.toSpecΓ))
  exact properSmoothRelative_isMonHom_of_one G (pointedCubicBase W) _
    (pointedCubicBaseMap_zero W G e he η[G] hs)

end FLT.Mazur.FCurve

namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsAffine S] (E : GeneralizedEllipticCurve S)
  (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (e : E.curve.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = E.curve.hom ≫ S.toSpecΓ)
/-- The original pulled cubic carries its established commutative group structure. -/
local instance unrestrictedPointedCubicCommGrp : CommGrpObj (pointedCubicBase W) :=
  pointedCubicBaseCommGrp W

/-- An original pointed presentation identifies both group laws without Noetherianity. -/
theorem pointedCubicGroupIso_isMonHom_unrestricted
    (hs : E.identitySection.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W) :
    IsMonHom (pointedCubicGroupIso E W e he).hom := by
  let _ := smooth_of_pointedCubic E W e he
  let _ := smooth_relativeDimension E
  let _ := smoothCurve_geometricallyIntegral E
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  let _ : IsMonHom (asIso E.inclusion).hom := isMonHom_ofIso (asIso E.inclusion)
  let _ : IsMonHom (pointedCubicBaseMap W E.curve e he) :=
    pointedCubicBaseMap_isMonHom_unrestricted W E.curve e he hs
  change IsMonHom ((asIso E.inclusion).hom ≫ pointedCubicBaseMap W E.curve e he)
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
