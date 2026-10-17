/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomNormalizationRelationSubgroup
public import FLT.Mazur.CyclicHomNormalizationSubgroupMarking
public import FLT.Mazur.CompatibleSubgroupMarkedConjugation

/-!
# The normalization relation retains actual subgroup labels

The compatible comparison between equal normalized parameters retains every
original orbit section and the chosen generator on the actual subgroup carrier.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Equality transport retains the chosen orbit labels on the actual subgroup. -/
theorem cyclicHomSubgroupParameterIso_orbit
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g)
    (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) (i : Multiplicative (ZMod n)) :
    (cyclicHomSubgroup n f hf).orbitMarking (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf) i ≫
        (cyclicHomSubgroupParameterIso n f g h hf hg).subgroup.hom =
      (cyclicHomSubgroup n g hg).orbitMarking (cyclicHomSourceMarking n g)
        (cyclicHomSubgroup_ideal n g hg) i := by
  subst g
  exact Category.comp_id _

/-- Equality transport also retains every auxiliary label of the full curve. -/
theorem cyclicHomSubgroupParameterIso_auxiliary
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g)
    (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      (cyclicHomSubgroupParameterIso n f g h hf hg).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i := by
  subst g
  exact Category.comp_id _

/-- Seal the actual normalization comparison before forming marked relations. -/
irreducible_def cyclicHomMarkedNormalizationIso
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hf : cyclicHomMultiplicationEquation n f = 0) :=
  cyclicHomNormalizationSubgroupIso n f hf

/-- Sealed normalization still retains every actual orbit label. -/
theorem cyclicHomMarkedNormalizationIso_orbit
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hf : cyclicHomMultiplicationEquation n f = 0) (i : Multiplicative (ZMod n)) :
    (cyclicHomSubgroup n (cyclicHomNormalizedPoint n f)
      (cyclicHomNormalization_equation n f hf)).orbitMarking
        (cyclicHomSourceMarking n (cyclicHomNormalizedPoint n f))
        (cyclicHomSubgroup_ideal n _ _) i ≫ (cyclicHomMarkedNormalizationIso n f hf).subgroup.hom =
      (cyclicHomSubgroup n f hf).orbitMarking (cyclicHomSourceMarking n f)
        (cyclicHomSubgroup_ideal n f hf) i := by
  rw [cyclicHomMarkedNormalizationIso_def]
  exact cyclicHomNormalizationSubgroupIso_orbit n f hf i

/-- Sealed normalization retains every full auxiliary label. -/
theorem cyclicHomMarkedNormalizationIso_auxiliary
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (hf : cyclicHomMultiplicationEquation n f = 0) (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (cyclicHomNormalizedPoint n f)) i ≫
      (cyclicHomMarkedNormalizationIso n f hf).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i := by
  rw [cyclicHomMarkedNormalizationIso_def]
  exact cyclicHomNormalizationSubgroupIso_auxiliary n f hf i

/-- Seal equality transport so relation sections do not expand its geometric carrier. -/
irreducible_def cyclicHomMarkedParameterIso
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g)
    (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) :=
  cyclicHomSubgroupParameterIso n f g h hf hg

/-- Sealed equality transport preserves actual orbit labels. -/
theorem cyclicHomMarkedParameterIso_orbit
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g)
    (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) (i : Multiplicative (ZMod n)) :
    (cyclicHomSubgroup n f hf).orbitMarking (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf) i ≫
        (cyclicHomMarkedParameterIso n f g h hf hg).subgroup.hom =
      (cyclicHomSubgroup n g hg).orbitMarking (cyclicHomSourceMarking n g)
        (cyclicHomSubgroup_ideal n g hg) i := by
  rw [cyclicHomMarkedParameterIso_def]
  exact cyclicHomSubgroupParameterIso_orbit n f g h hf hg i

/-- Sealed equality transport preserves full auxiliary labels. -/
theorem cyclicHomMarkedParameterIso_auxiliary
    (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left) (h : f = g)
    (hf : cyclicHomMultiplicationEquation n f = 0)
    (hg : cyclicHomMultiplicationEquation n g = 0) (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      (cyclicHomMarkedParameterIso n f g h hf hg).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i := by
  rw [cyclicHomMarkedParameterIso_def]
  exact cyclicHomSubgroupParameterIso_auxiliary n f g h hf hg i

attribute [local irreducible] auxiliarySchemeMarking cyclicHomSourceMarking
  cyclicHomNormalizedPoint cyclicHomSubgroup

variable (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)
  (hf : cyclicHomMultiplicationEquation n f = 0)
  (hg : cyclicHomMultiplicationEquation n g = 0)

/-- The actual full normalization relation with sealed geometric comparisons. -/
irreducible_def cyclicHomMarkedRelationSubgroupIso :=
  (cyclicHomMarkedNormalizationIso n f hf).symm.trans
    ((cyclicHomMarkedParameterIso n _ _ h
      (cyclicHomNormalization_equation n f hf) (cyclicHomNormalization_equation n g hg)).trans
        (cyclicHomMarkedNormalizationIso n g hg))

/-- The sealed relation is exactly the previously constructed actual subgroup comparison. -/
theorem cyclicHomMarkedRelationSubgroupIso_eq :
    cyclicHomMarkedRelationSubgroupIso n f g h hf hg =
      cyclicHomNormalizationRelationSubgroupIso n f g h hf hg := by
  rw [cyclicHomMarkedRelationSubgroupIso_def, cyclicHomMarkedNormalizationIso_def,
    cyclicHomMarkedNormalizationIso_def, cyclicHomMarkedParameterIso_def]
  rfl

/-- The relation comparison preserves every label in the original actual subgroup. -/
theorem cyclicHomMarkedRelationSubgroupIso_orbit (i : Multiplicative (ZMod n)) :
    (cyclicHomSubgroup n f hf).orbitMarking (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf) i ≫
        (cyclicHomMarkedRelationSubgroupIso n f g h hf hg).subgroup.hom =
      (cyclicHomSubgroup n g hg).orbitMarking (cyclicHomSourceMarking n g)
        (cyclicHomSubgroup_ideal n g hg) i := by
  rw [cyclicHomMarkedRelationSubgroupIso_def]
  exact CompatibleIso.subgroup_section_conjugate
    (cyclicHomMarkedNormalizationIso n f hf)
    (cyclicHomMarkedParameterIso n _ _ h _ _)
    (cyclicHomMarkedNormalizationIso n g hg) _ _ _ _
    (cyclicHomMarkedNormalizationIso_orbit n f hf i)
    (cyclicHomMarkedParameterIso_orbit n _ _ h _ _ i)
    (cyclicHomMarkedNormalizationIso_orbit n g hg i)

/-- The very same full subgroup relation retains all independent auxiliary labels. -/
theorem cyclicHomMarkedRelationSubgroupIso_auxiliary (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      (cyclicHomMarkedRelationSubgroupIso n f g h hf hg).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i := by
  rw [cyclicHomMarkedRelationSubgroupIso_def]
  exact CompatibleIso.group_section_conjugate
    (cyclicHomMarkedNormalizationIso n f hf)
    (cyclicHomMarkedParameterIso n (cyclicHomNormalizedPoint n f) (cyclicHomNormalizedPoint n g) h
      (cyclicHomNormalization_equation n f hf) (cyclicHomNormalization_equation n g hg))
    (cyclicHomMarkedNormalizationIso n g hg)
    (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i)
    (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (cyclicHomNormalizedPoint n f)) i)
    (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (cyclicHomNormalizedPoint n g)) i)
    (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i)
    (cyclicHomMarkedNormalizationIso_auxiliary n f hf i)
    (cyclicHomMarkedParameterIso_auxiliary n (cyclicHomNormalizedPoint n f)
      (cyclicHomNormalizedPoint n g) h (cyclicHomNormalization_equation n f hf)
      (cyclicHomNormalization_equation n g hg) i)
    (cyclicHomMarkedNormalizationIso_auxiliary n g hg i)

/-- Equal complete normalizations retain the specified original Cartier generators. -/
theorem cyclicHomMarkedRelationSubgroupIso_generator :
    (cyclicHomSubgroup n f hf).orbitGenerator (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf) ≫
        (cyclicHomMarkedRelationSubgroupIso n f g h hf hg).subgroup.hom =
      (cyclicHomSubgroup n g hg).orbitGenerator (cyclicHomSourceMarking n g)
        (cyclicHomSubgroup_ideal n g hg) := by
  dsimp only [orbitGenerator]
  exact cyclicHomMarkedRelationSubgroupIso_orbit n f g h hf hg (.ofAdd 1)

end FLT.Mazur.UniversalWeierstrass
