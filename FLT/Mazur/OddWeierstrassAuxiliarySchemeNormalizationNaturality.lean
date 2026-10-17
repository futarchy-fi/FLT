/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryValueNaturality
public import FLT.Mazur.OddWeierstrassAuxiliaryCoordinateExt
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationMarking

/-!
# Odd auxiliary normalization is natural on arbitrary schemes

The full normalization comparison carries every original auxiliary section to
its normalized section. Source naturality of that comparison identifies the
actual normalized parameter, without reconstructing points from global functions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T U : Scheme} (f : T ⟶ levelThree.left)

/-- Inverse normalization carries every original auxiliary section to its normalized section. -/
theorem auxiliarySchemeNormalizationGroupIso_inv_marking (a : Labels 3) :
    auxiliarySchemeMarking f a ≫ (auxiliarySchemeNormalizationGroupIso f).inv.hom.hom.hom =
      auxiliarySchemeMarking (auxiliarySchemeNormalizedPoint f) a := by
  let e := auxiliarySchemeNormalizationOverIso f
  apply (cancel_mono e.hom).mp
  change (_ ≫ e.inv) ≫ e.hom = _ ≫ e.hom
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  exact (auxiliarySchemeNormalizationGroupIso_marking f a).symm

/-- Every original auxiliary value lies over the original coefficient parameter. -/
theorem auxiliarySchemeValue_base (a : Labels 3) :
    (f ≫ (levelThreeMarking a).left) ≫ universalGroup.hom = f ≫ levelThree.hom := by
  rw [Category.assoc, (levelThreeMarking a).w]

/-- The normalized parameter's labels are the actual full group normalization of its labels. -/
theorem auxiliarySchemeNormalizedPoint_value_normalize (a : Labels 3) :
    auxiliarySchemeNormalizedPoint f ≫ (levelThreeMarking a).left =
      auxiliarySchemeNormalizedValue f (f ≫ (levelThreeMarking a).left)
        (auxiliarySchemeValue_base f a) := by
  have hl : pullback.lift (f ≫ (levelThreeMarking a).left) (𝟙 T)
      ((auxiliarySchemeValue_base f a).trans (Category.id_comp _).symm) =
    (auxiliarySchemeMarking f a).left := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (auxiliarySchemeMarking_fst f a).symm
    · exact (pullback.lift_snd _ _ _).trans (auxiliarySchemeMarking f a).w.symm
  rw [auxiliarySchemeNormalizedValue, hl, ← Category.assoc]
  have hm := congrArg Over.Hom.left (auxiliarySchemeNormalizationGroupIso_inv_marking f a)
  rw [show (auxiliarySchemeMarking f a).left ≫
      (auxiliarySchemeNormalizationGroupIso f).inv.hom.hom.hom.left =
      (auxiliarySchemeMarking (auxiliarySchemeNormalizedPoint f) a).left from hm]
  exact (auxiliarySchemeMarking_fst (auxiliarySchemeNormalizedPoint f) a).symm

/-- The entire normalized auxiliary point commutes with every source morphism. -/
theorem auxiliarySchemeNormalizedPoint_natural (k : U ⟶ T) :
    auxiliarySchemeNormalizedPoint (k ≫ f) = k ≫ auxiliarySchemeNormalizedPoint f := by
  apply auxiliarySchemePoint_ext _ _ (auxiliarySchemeNormalizedPoint_natural_base f k)
  intro a
  rw [Category.assoc, auxiliarySchemeNormalizedPoint_value_normalize,
    auxiliarySchemeNormalizedPoint_value_normalize]
  exact auxiliarySchemeNormalizedValue_natural_of_eq _ _ (auxiliarySchemeValue_base f a)
    k _ _ (auxiliarySchemeValue_base (k ≫ f) a) rfl (Category.assoc _ _ _)

end FLT.Mazur.OddWeierstrassParameter
