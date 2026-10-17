/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeneralizedCurveGroupIso
public import FLT.Mazur.GeneralizedCurveSmoothBaseDimension
public import FLT.Mazur.GeneralizedCurveSmoothIntegral
public import FLT.Mazur.ProperSmoothRelativePointedGroupHom

/-!
# Pointed curve isomorphisms of smooth generalized elliptic curves

The original proper smooth geometry forces a pointed curve isomorphism to preserve
the group laws. Its full DR extension retains the prescribed curve isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E F : GeneralizedEllipticCurve S)
  [Smooth E.curve.hom] [Smooth F.curve.hom]
  (c : E.curve ≅ F.curve) (hc : E.identitySection ≫ c.hom = F.identitySection)

/-- The group carrier comparison determined by the original curve comparison. -/
def pointedSmoothGroupIso : E.group ≅ F.group :=
  asIso E.inclusion ≪≫ c ≪≫ (asIso F.inclusion).symm

include hc in
/-- Rigidity forces the actual smooth-group comparison to preserve both group laws. -/
theorem pointedSmoothGroupIso_isMonHom : IsMonHom (pointedSmoothGroupIso E F c).hom := by
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  let _ : GrpObj F.curve := GrpObj.ofIso (asIso F.inclusion)
  let _ : IsMonHom (asIso E.inclusion).hom := isMonHom_ofIso (asIso E.inclusion)
  let _ : IsMonHom (asIso F.inclusion).hom := isMonHom_ofIso (asIso F.inclusion)
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : IsProper F.curve.hom := F.family.family.1
  let _ := E.smooth_relativeDimension
  let _ := E.smoothCurve_geometricallyIntegral
  have hu : η[E.curve] ≫ c.hom = η[F.curve] := by
    change (η[E.group] ≫ E.inclusion) ≫ c.hom = η[F.group] ≫ F.inclusion
    exact hc
  let _ : IsMonHom c.hom := FCurve.properSmoothRelative_isMonHom_of_one
    E.curve F.curve c.hom hu
  change IsMonHom ((asIso E.inclusion).hom ≫ c.hom ≫ (asIso F.inclusion).inv)
  infer_instance

/-- Every pointed smooth curve isomorphism lifts to the full DR category. -/
def pointedSmoothIso : E ≅ F := by
  let _ := pointedSmoothGroupIso_isMonHom E F c hc
  exact isoOfSmoothGroup E F (pointedSmoothGroupIso E F c)

/-- The DR lift retains the specified original curve comparison exactly. -/
theorem pointedSmoothIso_curve : (pointedSmoothIso E F c hc).hom.curve = c.hom := by
  change (smoothGroupCurveIso E F (pointedSmoothGroupIso E F c)).hom = c.hom
  simp only [smoothGroupCurveIso, pointedSmoothGroupIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.GeneralizedEllipticCurve
