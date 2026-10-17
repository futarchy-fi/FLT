/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarkingComparison
public import FLT.Mazur.GroupSchemeBaseChangeSections

/-!
# Normalization preserves the actual universal labels on arbitrary schemes

The normalization group isomorphism carries the displayed normalized universal
marking to the displayed original marking, including the identity label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup

variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- Pullback to the actual source retains the complete normalization marking equation. -/
theorem auxiliarySchemeNormalization_lift_marking (a : Labels 3) :
    OverPullbackSection.lift T.toSpecΓ (auxiliaryNormalizedGroup f.appTop.hom).X
      (auxiliaryNormalizedParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a) ≫
        ((Over.pullback T.toSpecΓ).mapCommGrp.map
          (auxiliaryNormalizationGroupIso f.appTop.hom).hom).hom.hom.hom =
            OverPullbackSection.lift T.toSpecΓ (auxiliaryPullbackGroup f.appTop.hom).X
              (auxiliaryOriginalParameterMarking f.appTop.hom
                (auxiliarySchemeRelativePoint f) a) :=
  GroupSchemeBaseChange.lift_map_eq T.toSpecΓ
    (auxiliaryNormalizationGroupIso f.appTop.hom).hom _ _
    (auxiliaryNormalizedParameterMarking_compare f.appTop.hom (auxiliarySchemeRelativePoint f) a)

/-- Normalization carries all actual normalized universal sections to the original sections. -/
theorem auxiliarySchemeNormalizationGroupIso_marking (a : Labels 3) :
    auxiliarySchemeMarking (auxiliarySchemeNormalizedPoint f) a ≫
      (auxiliarySchemeNormalizationGroupIso f).hom.hom.hom.hom =
        auxiliarySchemeMarking f a := by
  let eN := (CommGrp.forget (Over T)).mapIso (auxiliarySchemeNormalizedCoefficientGroupIso f)
  let eO := (CommGrp.forget (Over T)).mapIso (auxiliarySchemeCoefficientGroupIso f)
  let m := ((Over.pullback T.toSpecΓ).mapCommGrp.map
    (auxiliaryNormalizationGroupIso f.appTop.hom).hom).hom.hom.hom
  let sN := OverPullbackSection.lift T.toSpecΓ (auxiliaryNormalizedGroup f.appTop.hom).X
    (auxiliaryNormalizedParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a)
  let sO := OverPullbackSection.lift T.toSpecΓ (auxiliaryPullbackGroup f.appTop.hom).X
    (auxiliaryOriginalParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a)
  have hN : sN ≫ eN.hom = auxiliarySchemeMarking (auxiliarySchemeNormalizedPoint f) a :=
    auxiliarySchemeNormalizedCoefficientGroupIso_marking f a
  have hO : sO ≫ eO.hom = auxiliarySchemeMarking f a :=
    auxiliarySchemeCoefficientGroupIso_marking f a
  have hM : sN ≫ m = sO := auxiliarySchemeNormalization_lift_marking f a
  rw [auxiliarySchemeNormalizationGroupIso_def]
  change _ ≫ (eN.inv ≫ m ≫ eO.hom) = _
  rw [← hN, Category.assoc, eN.hom_inv_id_assoc, ← Category.assoc, hM, hO]

end FLT.Mazur.OddWeierstrassParameter
