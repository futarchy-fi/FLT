/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryCoefficientNaturality
public import FLT.Mazur.OddWeierstrassAuxiliaryCubicProjection

/-!
# Actual cubic projections of arbitrary-source group families

The coefficient comparison gives each source family its original proper cubic
projection. This projection and the source structure map jointly detect maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- The original cubic projection recovers the displayed universal-family projection. -/
@[reassoc] theorem auxiliarySchemeOriginalCubicProjection_coefficient :
    auxiliarySchemeOriginalCubicProjection f ≫
        auxiliaryOriginalCoefficientProjection f.appTop.hom =
      pullback.fst universalGroup.hom (f ≫ levelThree.hom) := by
  rw [auxiliarySchemeOriginalCubicProjection, Category.assoc,
    ← auxiliaryCoefficientGroupIso_proper_fst, ← auxiliarySchemeCoefficientGroupIso_fst]
  have h := congrArg (fun z ↦ z.hom.hom.hom.left)
    (auxiliarySchemeCoefficientGroupIso f).inv_hom_id
  change (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.left ≫
    (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom.left = 𝟙 _ at h
  rw [← Category.assoc, h, Category.id_comp]

/-- The normalized cubic projection recovers the displayed universal-family projection. -/
@[reassoc] theorem auxiliarySchemeNormalizedCubicProjection_coefficient :
    auxiliarySchemeNormalizedCubicProjection f ≫
        auxiliaryNormalizedCoefficientProjection f.appTop.hom =
      pullback.fst universalGroup.hom
        (auxiliarySchemeNormalizedPoint f ≫ levelThree.hom) := by
  rw [auxiliarySchemeNormalizedCubicProjection, Category.assoc,
    ← auxiliaryNormalizedCoefficientGroupIso_proper_fst,
    ← auxiliarySchemeNormalizedCoefficientGroupIso_fst]
  have h := congrArg (fun z ↦ z.hom.hom.hom.left)
    (auxiliarySchemeNormalizedCoefficientGroupIso f).inv_hom_id
  change (auxiliarySchemeNormalizedCoefficientGroupIso f).inv.hom.hom.hom.left ≫
    (auxiliarySchemeNormalizedCoefficientGroupIso f).hom.hom.hom.hom.left = 𝟙 _ at h
  rw [← Category.assoc, h, Category.id_comp]

end FLT.Mazur.OddWeierstrassParameter
