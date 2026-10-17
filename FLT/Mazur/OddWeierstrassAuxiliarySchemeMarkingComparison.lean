/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarking
public import FLT.Mazur.OddWeierstrassNormalizedParameterMarking
public import FLT.Mazur.OverPullbackSection

/-!
# Odd coefficient comparisons retain all actual scheme labels

Both coefficient comparisons identify the faithful parameter markings with
the displayed universal sections on arbitrary source schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup

/-- The original coefficient comparison retains every actual original label. -/
theorem auxiliarySchemeCoefficientGroupIso_marking (a : Labels 3) :
    OverPullbackSection.lift T.toSpecΓ (auxiliaryPullbackGroup f.appTop.hom).X
      (auxiliaryOriginalParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a) ≫
        (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom =
          auxiliarySchemeMarking f a := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, auxiliarySchemeCoefficientGroupIso_fst,
    ← Category.assoc, OverPullbackSection.lift_fst]
  exact auxiliaryOriginalParameterMarking_fst _ _ a

/-- The normalized coefficient comparison retains every actual normalized label. -/
theorem auxiliarySchemeNormalizedCoefficientGroupIso_marking (a : Labels 3) :
    OverPullbackSection.lift T.toSpecΓ (auxiliaryNormalizedGroup f.appTop.hom).X
      (auxiliaryNormalizedParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a) ≫
        (auxiliarySchemeNormalizedCoefficientGroupIso f).hom.hom.hom.hom =
          auxiliarySchemeMarking (auxiliarySchemeNormalizedPoint f) a := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, auxiliarySchemeNormalizedCoefficientGroupIso_fst,
    ← Category.assoc, OverPullbackSection.lift_fst]
  exact auxiliaryNormalizedParameterMarking_fst _ _ a

end FLT.Mazur.OddWeierstrassParameter
