/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryCubicProjection

/-!
# The full scheme normalization retains the actual proper normalization

The coefficient comparisons cancel before taking the cubic projection. The
resulting square controls the entire family, independently of its markings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- Inverse normalization on the actual source family retains the original proper map. -/
@[reassoc] theorem auxiliarySchemeNormalizationGroupIso_inv_cubic :
    (auxiliarySchemeNormalizationGroupIso f).inv.hom.hom.hom.left ≫
        auxiliarySchemeNormalizedCubicProjection f =
      auxiliarySchemeOriginalCubicProjection f ≫
        (auxiliaryProperNormalization f.appTop.hom).inv := by
  have h := congrArg (fun z ↦ z.hom.hom.hom.left)
    (auxiliarySchemeNormalizedCoefficientGroupIso f).hom_inv_id
  change (auxiliarySchemeNormalizedCoefficientGroupIso f).hom.hom.hom.hom.left ≫
    (auxiliarySchemeNormalizedCoefficientGroupIso f).inv.hom.hom.hom.left = 𝟙 _ at h
  rw [auxiliarySchemeNormalizationGroupIso_def,
    auxiliarySchemeNormalizedCubicProjection, auxiliarySchemeOriginalCubicProjection]
  change ((_ ≫ ((Over.pullback T.toSpecΓ).mapCommGrp.map
    (auxiliaryNormalizationGroupIso f.appTop.hom).inv).hom.hom.hom.left) ≫ _) ≫ _ = _
  simp only [Iso.symm_inv, Category.assoc, reassoc_of% h]
  rw [GroupSchemeBaseChange.map_hom_fst, auxiliaryNormalizationGroupIso_inv]

/-- Normalization on the actual source family retains the forward proper comparison. -/
@[reassoc] theorem auxiliarySchemeNormalizationGroupIso_hom_cubic :
    (auxiliarySchemeNormalizationGroupIso f).hom.hom.hom.hom.left ≫
        auxiliarySchemeOriginalCubicProjection f =
      auxiliarySchemeNormalizedCubicProjection f ≫
        (auxiliaryProperNormalization f.appTop.hom).hom := by
  have h := congrArg (fun z ↦ z.hom.hom.hom.left)
    (auxiliarySchemeCoefficientGroupIso f).hom_inv_id
  change (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom.left ≫
    (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.left = 𝟙 _ at h
  rw [auxiliarySchemeNormalizationGroupIso_def,
    auxiliarySchemeNormalizedCubicProjection, auxiliarySchemeOriginalCubicProjection]
  change (_ ≫ ((Over.pullback T.toSpecΓ).mapCommGrp.map
    (auxiliaryNormalizationGroupIso f.appTop.hom).hom).hom.hom.hom.left ≫ _) ≫ _ = _
  simp only [Iso.symm_hom, Category.assoc, reassoc_of% h]
  rw [GroupSchemeBaseChange.map_hom_fst, auxiliaryNormalizationGroupIso_hom]

end FLT.Mazur.OddWeierstrassParameter
