/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeGroupComparison
public import FLT.Mazur.GroupMarkingTransportEquations

/-!
# The actual universal auxiliary marking over every source scheme

Every scheme-valued level point gives all sixteen sections of its actual
universal group pullback. Projection recovers the displayed universal labels,
and that projection determines each section uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelFour.left)

/-- The actual level point regarded over its own original coefficient map. -/
def auxiliarySchemeGroupPoint :
    (Over.map (f ≫ levelFour.hom)).obj (𝟙_ (Over T)) ⟶ levelFour :=
  Over.homMk f (Category.id_comp _).symm

/-- The displayed universal labeling on the actual pulled-back group family. -/
def auxiliarySchemeMarking :
    Labels 4 →* (𝟙_ (Over T) ⟶ (auxiliarySchemeGroup f).X) :=
  GroupMarkingBaseChange.marking _
    (integralCurveGroup smoothEquation smoothEquation_discriminant).X _
    (AuxiliaryLevel.markingOf universalGroup (Labels 4)
      (auxiliarySchemeGroupPoint f ≫ auxiliaryInclusion 4))

/-- Every group label projects to its original universal auxiliary section. -/
@[reassoc] theorem auxiliarySchemeMarking_fst (a : Labels 4) :
    (auxiliarySchemeMarking f a).left ≫
      pullback.fst universalGroup.hom (f ≫ levelFour.hom) =
        f ≫ (auxiliaryMarking 4 a).left := by
  exact (GroupMarkingBaseChange.marking_fst _
    (integralCurveGroup smoothEquation smoothEquation_discriminant).X _ _ a).trans
      (congrArg Over.Hom.left
        (AuxiliaryLevel.markingOf_comp universalGroup (Labels 4)
          (auxiliarySchemeGroupPoint f) (auxiliaryInclusion 4) a))

/-- Projection uniquely determines a section of the actual auxiliary family. -/
theorem auxiliarySchemeMarking_ext (a : Labels 4)
    (s : 𝟙_ (Over T) ⟶ (auxiliarySchemeGroup f).X)
    (h : s.left ≫ pullback.fst universalGroup.hom (f ≫ levelFour.hom) =
      f ≫ (auxiliaryMarking 4 a).left) : s = auxiliarySchemeMarking f a := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext (h.trans (auxiliarySchemeMarking_fst f a).symm)
  exact s.w.trans (auxiliarySchemeMarking f a).w.symm

/-- The actual universal marking is faithful on every nonempty source scheme. -/
theorem auxiliarySchemeMarking_injective [Nonempty T] :
    Function.Injective (auxiliarySchemeMarking f) := by
  unfold auxiliarySchemeMarking
  apply (GroupMarkingBaseChange.marking_injective_iff _ _ _ _).mpr
  let _ : Nonempty ((Over.map (f ≫ levelFour.hom)).obj (𝟙_ (Over T))).left :=
    inferInstanceAs (Nonempty T)
  exact auxiliaryMarking_injective 4 (auxiliarySchemeGroupPoint f)

/-- All actual scheme labels satisfy the original order-four equation. -/
theorem auxiliarySchemeMarking_pow (a : Labels 4) : auxiliarySchemeMarking f a ^ 4 = 1 :=
  GroupMarkingTransport.marking_pow_eq_one _ (auxiliarySchemeMarking f) a 4 (labels_pow 4 a)

end FLT.Mazur.UniversalWeierstrass
