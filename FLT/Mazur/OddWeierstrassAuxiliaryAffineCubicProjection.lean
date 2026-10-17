/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryCubicProjection
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarkingSections

/-!
# Affine source families recover their original proper cubics

The original cubic projection is an isomorphism on an affine source. Its
markings project to the evaluated original sections, including the identity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- Over an affine source the original cubic projection is an isomorphism. -/
instance auxiliarySchemeOriginalCubicProjection_isIso [IsAffine T] :
    IsIso (auxiliarySchemeOriginalCubicProjection f) := by
  let _ : IsIso (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.left := by
    change IsIso (((CommGrp.forget (Over T)) ⋙ Over.forget T).mapIso
      (auxiliarySchemeCoefficientGroupIso f)).inv
    infer_instance
  unfold auxiliarySchemeOriginalCubicProjection
  infer_instance

/-- The coefficient comparison followed by the cubic projection is the pullback projection. -/
@[reassoc] theorem auxiliarySchemeCoefficientGroupIso_cubic :
    (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom.left ≫
      auxiliarySchemeOriginalCubicProjection f =
        pullback.fst (auxiliaryPullbackGroup f.appTop.hom).X.hom T.toSpecΓ := by
  have hi := congrArg (fun z ↦ z.hom.hom.hom.left)
    (auxiliarySchemeCoefficientGroupIso f).hom_inv_id
  change (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom.left ≫
    (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.left = 𝟙 _ at hi
  rw [auxiliarySchemeOriginalCubicProjection, ← Category.assoc, hi, Category.id_comp]

/-- Projection of every full auxiliary label is its original relative cubic value. -/
theorem auxiliarySchemeMarking_cubic (a : Labels 3) :
    (auxiliarySchemeMarking f a).left ≫ auxiliarySchemeOriginalCubicProjection f =
      (auxiliaryOriginalParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a).left := by
  rw [← auxiliarySchemeCoefficientGroupIso_marking, Over.comp_left, Category.assoc,
    auxiliarySchemeCoefficientGroupIso_cubic, OverPullbackSection.lift_fst]

/-- Every nonidentity auxiliary label recovers its actual evaluated proper section. -/
theorem auxiliarySchemeMarking_cubic_section (a : Labels 3) (ha : a ≠ 1) :
    (auxiliarySchemeMarking f a).left ≫ auxiliarySchemeOriginalCubicProjection f =
      T.toSpecΓ ≫ auxiliaryPullbackSection f.appTop.hom a ha :=
  (auxiliarySchemeMarking_cubic f a).trans (auxiliarySchemeOriginalParameterMarking_section f a ha)

/-- The identity auxiliary label projects to the actual zero section. -/
theorem auxiliarySchemeMarking_cubic_one :
    (auxiliarySchemeMarking f 1).left ≫ auxiliarySchemeOriginalCubicProjection f =
      T.toSpecΓ ≫ integralCurveZero (auxiliaryPullbackEquation f.appTop.hom) := by
  rw [auxiliarySchemeMarking_cubic, map_one]
  change (𝟙 _ ≫ T.toSpecΓ ≫ integralCurveZero _) = _
  exact Category.id_comp _

end FLT.Mazur.OddWeierstrassParameter
