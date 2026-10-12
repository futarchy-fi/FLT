/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicBaseGroupIso
public import FLT.Mazur.GeneralizedCurveSmoothBaseDimension
public import FLT.Mazur.GeneralizedCurveSmoothIntegral
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# The original generalized group in any pointed cubic chart

An identity-preserving complete cubic presentation induces a group isomorphism
with the established cubic law over the actual base. Its projection is the
specified complete curve map composed with the original smooth inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} [IsAffine S] (E : GeneralizedEllipticCurve S)
  (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (e : E.curve.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = E.curve.hom ≫ S.toSpecΓ)

include he in
/-- A nonsingular original cubic comparison proves smoothness of the entire original curve. -/
theorem smooth_of_pointedCubic : Smooth E.curve.hom := by
  let f := pointedCubicBaseMap W E.curve e he
  let _ := integralCurveStructure_smooth W (WeierstrassCurve.IsElliptic.isUnit (W := W))
  let _ : Smooth (pointedCubicBase W).hom :=
    inferInstanceAs (Smooth (pullback.snd (integralCurveStructure W) S.toSpecΓ))
  have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget S).map f))
  rw [← f.w]
  infer_instance

/-- The original group comparison uses the original inclusion and the complete cubic lift. -/
def pointedCubicGroupIso : E.group ≅ pointedCubicBase W := by
  let _ := smooth_of_pointedCubic E W e he
  exact asIso E.inclusion ≪≫ asIso (pointedCubicBaseMap W E.curve e he)

/-- Every original section projects through precisely the given complete cubic map. -/
@[reassoc] theorem pointedCubicGroupIso_fst :
    (pointedCubicGroupIso E W e he).hom.left ≫
      pullback.fst (integralCurveStructure W) S.toSpecΓ = E.inclusion.left ≫ e.hom := by
  change (E.inclusion.left ≫ (pointedCubicBaseMap W E.curve e he).left) ≫ _ = _
  rw [Category.assoc, pointedCubicBaseMap_fst]

/-- Use the established pulled-back cubic operations in the comparison statements. -/
local instance : CommGrpObj (pointedCubicBase W) := pointedCubicBaseCommGrp W

/-- The original identity equation forces compatibility with the established cubic group law. -/
theorem pointedCubicGroupIso_isMonHom [IsLocallyNoetherian S]
    (hs : E.identitySection.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W) :
    IsMonHom (pointedCubicGroupIso E W e he).hom := by
  let _ := smooth_of_pointedCubic E W e he
  let _ := smooth_relativeDimension E
  let _ := smoothCurve_geometricallyIntegral E
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  let _ : IsMonHom (asIso E.inclusion).hom := isMonHom_ofIso (asIso E.inclusion)
  let _ : IsMonHom (pointedCubicBaseMap W E.curve e he) :=
    pointedCubicBaseMap_isMonHom W E.curve e he hs
  change IsMonHom ((asIso E.inclusion).hom ≫ pointedCubicBaseMap W E.curve e he)
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
