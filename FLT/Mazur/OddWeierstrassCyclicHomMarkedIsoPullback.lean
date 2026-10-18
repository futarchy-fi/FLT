/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSourceGroupComparison
public import FLT.Mazur.OddWeierstrassCyclicHomMarkedFamilyRelation
public import FLT.Mazur.UniversalWeierstrassCyclicRelationOriginalMarking

/-!
# Pullback of specified independently marked group comparisons

The actual pulled-back isomorphism retains both original markings, including
coincident cyclic sections. No condition on the source scheme is imposed.
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

/-- Pull back the specified comparison and identify the actual original source families. -/
irreducible_def cyclicHomMarkedIsoPullback :
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n (k ≫ f)) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n (k ≫ g)) :=
  (cyclicHomSourceGroupIso n f k).symm ≪≫
    (Over.pullback k).mapCommGrp.mapIso e ≪≫ cyclicHomSourceGroupIso n g k

/-- Pullback retains each of the independent auxiliary labels. -/
theorem cyclicHomMarkedIsoPullback_auxiliary
    (ha : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
      e.hom.hom.hom.hom = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)
    (c : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ f)) c ≫
      (cyclicHomMarkedIsoPullback n f g e k).hom.hom.hom.hom =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ g)) c := by
  apply auxiliarySchemeSection_iso_congr _ _ _ _ (cyclicHomMarkedIsoPullback_def n f g e k)
  apply auxiliarySchemeSection_conjugate
    (cyclicHomSourceGroupIso n f k) ((Over.pullback k).mapCommGrp.mapIso e)
    (cyclicHomSourceGroupIso n g k)
    _ (GroupSectionBaseChange.pullSection k
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c))
    (GroupSectionBaseChange.pullSection k
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)) _
  · exact cyclicHomSourceGroupIso_auxiliary n f k c
  · change _ ≫ (Over.pullback k).map e.hom.hom.hom.hom = _
    rw [← GroupSectionBaseChange.section_comp, ha c]
  · exact cyclicHomSourceGroupIso_auxiliary n g k c

/-- Pullback retains every cyclic label without requiring distinct sections. -/
theorem cyclicHomMarkedIsoPullback_cyclic
    (hc : ∀ c : Multiplicative (ZMod n), cyclicHomSourceMarking n f c ≫
      e.hom.hom.hom.hom = cyclicHomSourceMarking n g c) (c : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n (k ≫ f) c ≫
      (cyclicHomMarkedIsoPullback n f g e k).hom.hom.hom.hom =
        cyclicHomSourceMarking n (k ≫ g) c := by
  apply auxiliarySchemeSection_iso_congr _ _ _ _ (cyclicHomMarkedIsoPullback_def n f g e k)
  apply auxiliarySchemeSection_conjugate
    (cyclicHomSourceGroupIso n f k) ((Over.pullback k).mapCommGrp.mapIso e)
    (cyclicHomSourceGroupIso n g k)
    _ (GroupSectionBaseChange.pullSection k (cyclicHomSourceMarking n f c))
    (GroupSectionBaseChange.pullSection k (cyclicHomSourceMarking n g c)) _
  · exact cyclicHomSourceGroupIso_marking n f k c
  · change _ ≫ (Over.pullback k).map e.hom.hom.hom.hom = _
    rw [← GroupSectionBaseChange.section_comp, hc c]
  · exact cyclicHomSourceGroupIso_marking n g k c

end FLT.Mazur.OddWeierstrassParameter
