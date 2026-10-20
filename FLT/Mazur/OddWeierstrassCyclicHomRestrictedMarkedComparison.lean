/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomMarkedIsoPullback
public import FLT.Mazur.GroupSectionRestrictionEquality
public import FLT.Mazur.UniversalWeierstrassCyclicRelationOriginalMarking

/-!
# Exact restricted marking matches under the original pulled comparison

Equalities after restricting original scheme maps give exact markings under
the canonical pulled comparison. Independent source and target labels are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels auxiliarySchemeSection_iso_congr auxiliarySchemeSection_conjugate)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g)) (k : U ⟶ T)

/-- Pullback retains each of the independent auxiliary labels. -/
theorem cyclicHomMarkedIsoPullback_auxiliary_of_restriction
    (i j : Labels 3)
    (ha : k ≫ (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i).left ≫
      e.hom.hom.hom.hom.left = k ≫ (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) j).left) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ f)) i ≫
      (cyclicHomMarkedIsoPullback n f g e k).hom.hom.hom.hom =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ g)) j := by
  apply auxiliarySchemeSection_iso_congr _ _ _ _ (cyclicHomMarkedIsoPullback_def n f g e k)
  apply auxiliarySchemeSection_conjugate
    (cyclicHomSourceGroupIso n f k) ((Over.pullback k).mapCommGrp.mapIso e)
    (cyclicHomSourceGroupIso n g k)
    _ (GroupSectionBaseChange.pullSection k
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i))
    (GroupSectionBaseChange.pullSection k
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) j)) _
  · exact cyclicHomSourceGroupIso_auxiliary n f k i
  · change _ ≫ (Over.pullback k).map e.hom.hom.hom.hom = _
    exact GroupSectionBaseChange.pullSection_comp_eq k _ _ _ ha
  · exact cyclicHomSourceGroupIso_auxiliary n g k j

/-- Pullback retains every cyclic label without requiring distinct sections. -/
theorem cyclicHomMarkedIsoPullback_cyclic_of_restriction
    (i j : Multiplicative (ZMod n))
    (hc : k ≫ (cyclicHomSourceMarking n f i).left ≫ e.hom.hom.hom.hom.left =
      k ≫ (cyclicHomSourceMarking n g j).left) :
    cyclicHomSourceMarking n (k ≫ f) i ≫
      (cyclicHomMarkedIsoPullback n f g e k).hom.hom.hom.hom =
        cyclicHomSourceMarking n (k ≫ g) j := by
  apply auxiliarySchemeSection_iso_congr _ _ _ _ (cyclicHomMarkedIsoPullback_def n f g e k)
  apply auxiliarySchemeSection_conjugate
    (cyclicHomSourceGroupIso n f k) ((Over.pullback k).mapCommGrp.mapIso e)
    (cyclicHomSourceGroupIso n g k)
    _ (GroupSectionBaseChange.pullSection k (cyclicHomSourceMarking n f i))
    (GroupSectionBaseChange.pullSection k (cyclicHomSourceMarking n g j)) _
  · exact cyclicHomSourceGroupIso_marking n f k i
  · change _ ≫ (Over.pullback k).map e.hom.hom.hom.hom = _
    exact GroupSectionBaseChange.pullSection_comp_eq k _ _ _ hc
  · exact cyclicHomSourceGroupIso_marking n g k j

end FLT.Mazur.OddWeierstrassParameter
