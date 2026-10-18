/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationAuxiliaryMarking
public import FLT.Mazur.UniversalWeierstrassCyclicRelationOriginalMarking

/-!
# Equal normalizations compare the original independent marked families

Equality transport between the complete normalized parameters is conjugated
with the actual group normalizations. Both original markings are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels auxiliarySchemeSection_iso_congr auxiliarySchemeSection_conjugate)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Equal unrestricted parameters give the canonical equality comparison of their groups. -/
irreducible_def cyclicHomParameterGroupIso
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g) :
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
  eqToIso (congrArg (fun p ↦ auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n p)) h)

/-- Equality of the full parameter retains all independent auxiliary labels. -/
theorem cyclicHomParameterGroupIso_auxiliary
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g) (c : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
      (cyclicHomParameterGroupIso n f g h).hom.hom.hom.hom =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c := by
  subst g
  rw [cyclicHomParameterGroupIso_def]
  exact Category.comp_id _

/-- Equality transport retains every cyclic section without any distinctness assumption. -/
theorem cyclicHomParameterGroupIso_cyclic
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g) (c : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n f c ≫ (cyclicHomParameterGroupIso n f g h).hom.hom.hom.hom =
      cyclicHomSourceMarking n g c := by
  subst g
  rw [cyclicHomParameterGroupIso_def]
  exact Category.comp_id _

attribute [local irreducible] auxiliarySchemeMarking
  cyclicHomSourceMarking cyclicHomNormalizedPoint

variable (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)

/-- The actual original groups are compared through their equal full normalizations. -/
irreducible_def cyclicHomNormalizationRelationIso :
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
  (cyclicHomNormalizationGroupIso n f).symm ≪≫
    cyclicHomParameterGroupIso n _ _ h ≪≫ cyclicHomNormalizationGroupIso n g

/-- The constructed original comparison preserves every auxiliary label. -/
theorem cyclicHomNormalizationRelationIso_auxiliary (c : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
      (cyclicHomNormalizationRelationIso n f g h).hom.hom.hom.hom =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c :=
  auxiliarySchemeSection_iso_congr _ _ (cyclicHomNormalizationRelationIso n f g h) _
    (cyclicHomNormalizationRelationIso_def n f g h)
    (auxiliarySchemeSection_conjugate (cyclicHomNormalizationGroupIso n f)
      (cyclicHomParameterGroupIso n (cyclicHomNormalizedPoint n f)
        (cyclicHomNormalizedPoint n g) h) (cyclicHomNormalizationGroupIso n g)
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c)
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (cyclicHomNormalizedPoint n f)) c)
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (cyclicHomNormalizedPoint n g)) c)
      (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)
      (cyclicHomNormalizationGroupIso_auxiliary n f c)
      (cyclicHomParameterGroupIso_auxiliary n
        (cyclicHomNormalizedPoint n f) (cyclicHomNormalizedPoint n g) h c)
      (cyclicHomNormalizationGroupIso_auxiliary n g c))

/-- The constructed original comparison preserves every cyclic label, including repetitions. -/
theorem cyclicHomNormalizationRelationIso_cyclic (c : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n f c ≫
      (cyclicHomNormalizationRelationIso n f g h).hom.hom.hom.hom =
        cyclicHomSourceMarking n g c :=
  auxiliarySchemeSection_iso_congr _ _ (cyclicHomNormalizationRelationIso n f g h) _
    (cyclicHomNormalizationRelationIso_def n f g h)
    (auxiliarySchemeSection_conjugate (cyclicHomNormalizationGroupIso n f)
      (cyclicHomParameterGroupIso n (cyclicHomNormalizedPoint n f)
        (cyclicHomNormalizedPoint n g) h) (cyclicHomNormalizationGroupIso n g)
      (cyclicHomSourceMarking n f c) (cyclicHomSourceMarking n (cyclicHomNormalizedPoint n f) c)
      (cyclicHomSourceMarking n (cyclicHomNormalizedPoint n g) c) (cyclicHomSourceMarking n g c)
      (cyclicHomNormalizationGroupIso_marking n f c)
      (cyclicHomParameterGroupIso_cyclic n
        (cyclicHomNormalizedPoint n f) (cyclicHomNormalizedPoint n g) h c)
      (cyclicHomNormalizationGroupIso_marking n g c))

end FLT.Mazur.OddWeierstrassParameter
