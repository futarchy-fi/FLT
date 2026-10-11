/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeMarking
public import FLT.Mazur.UniversalWeierstrassAuxiliaryFullMarkingSections
public import FLT.Mazur.GroupSchemeBaseChangeComparison
public import FLT.Mazur.OverPullbackSection

/-!
# Coefficient comparisons retain all actual scheme labels

The original and normalized coefficient comparisons identify the previously
constructed full markings with the displayed universal labels. The source may
be any scheme; no affine presentation is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelFour.left)

/-- The original arbitrary-source coefficient comparison retains its actual projection. -/
@[reassoc] theorem auxiliarySchemeCoefficientGroupIso_fst :
    (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (f ≫ levelFour.hom) =
        pullback.fst (auxiliaryPullbackGroup f.appTop.hom).X.hom T.toSpecΓ ≫
          (auxiliaryCoefficientGroupIso f.appTop.hom).hom.hom.hom.hom.left ≫
            pullback.fst universalGroup.hom (auxiliaryCoefficientBase f.appTop.hom) := by
  rw [auxiliarySchemeCoefficientGroupIso_def]
  exact GroupSchemeBaseChange.coefficientComparison_fst _ _ _ _ _ _ _

/-- The normalized arbitrary-source coefficient comparison retains its actual projection. -/
@[reassoc] theorem auxiliarySchemeNormalizedCoefficientGroupIso_fst :
    (auxiliarySchemeNormalizedCoefficientGroupIso f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom
        (auxiliarySchemeNormalizedPoint f ≫ levelFour.hom) =
          pullback.fst (auxiliaryNormalizedGroup f.appTop.hom).X.hom T.toSpecΓ ≫
            (auxiliaryNormalizedCoefficientGroupIso f.appTop.hom).hom.hom.hom.hom.left ≫
              pullback.fst universalGroup.hom
                (auxiliaryNormalizedCoefficientBase f.appTop.hom) := by
  rw [auxiliarySchemeNormalizedCoefficientGroupIso_def]
  exact GroupSchemeBaseChange.coefficientComparison_fst _ _ _ _ _ _ _

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryCoefficientGroupIso auxiliaryNormalizedCoefficientGroupIso

/-- The original coefficient comparison carries every full label to its displayed section. -/
theorem auxiliarySchemeCoefficientGroupIso_marking (a : Labels 4) :
    OverPullbackSection.lift T.toSpecΓ (auxiliaryPullbackGroup f.appTop.hom).X
      (auxiliaryFullPullbackMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a) ≫
        (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom =
          auxiliarySchemeMarking f a := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, auxiliarySchemeCoefficientGroupIso_fst,
    ← Category.assoc, OverPullbackSection.lift_fst, ← Category.assoc, ← Over.comp_left]
  exact (congrArg (fun s => s.left ≫
    pullback.fst universalGroup.hom (auxiliaryCoefficientBase f.appTop.hom))
      (auxiliaryFullPullbackMarking_compare f.appTop.hom (auxiliarySchemeRelativePoint f) a)).trans
        (auxiliaryFullCoefficientMarking_fst f.appTop.hom (auxiliarySchemeRelativePoint f) a)

/-- The normalized coefficient comparison carries every full label to its displayed section. -/
theorem auxiliarySchemeNormalizedCoefficientGroupIso_marking (a : Labels 4) :
    OverPullbackSection.lift T.toSpecΓ (auxiliaryNormalizedGroup f.appTop.hom).X
      (auxiliaryFullNormalizedMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a) ≫
        (auxiliarySchemeNormalizedCoefficientGroupIso f).hom.hom.hom.hom =
          auxiliarySchemeMarking (auxiliarySchemeNormalizedPoint f) a := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, auxiliarySchemeNormalizedCoefficientGroupIso_fst,
    ← Category.assoc, OverPullbackSection.lift_fst, auxiliarySchemeNormalizedPoint_marking,
    auxiliaryNormalizedUniversalMarking_left, auxiliaryNormalizedUniversalPullbackMarking_left,
    Category.assoc]

end FLT.Mazur.UniversalWeierstrass
