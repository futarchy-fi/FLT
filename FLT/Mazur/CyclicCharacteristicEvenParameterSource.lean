/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenNormalizedAuxiliary

/-!
# The original source of an arbitrary even normalized parameter

Compare an actual normalized chart test directly with its unnormalized source
construction. Both the auxiliary labels and the specified orbit generator are
retained, and normalizing this original parameter recovers the given test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open UniversalWeierstrass GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (v : T ⟶ normalizedLocus n false)
local notation "l" => v ≫ cyclicHomNormalizedLocusInclusion n
local notation "f" => l ≫ cyclicHomUniversalMultiplicationLocusInclusion n
local notation "hf" => cyclicHomMultiplicationEquation_zero_comp n
  (cyclicHomUniversalMultiplicationLocusInclusion n) l (cyclicHomUniversalLocus_equation_zero n)
local notation "H" => cyclicHomSubgroup n f hf
local notation "hH" => cyclicHomSubgroup_ideal n f hf

/-- Renormalizing the original parameter of a normalized chart test recovers that test. -/
theorem evenNormalizedParameter_point : cyclicHomNormalizedLocusPoint n f hf = v := by
  rw [← cyclicHomLocusNormalization_comp, Category.assoc,
    cyclicHomNormalizedLocusInclusion_normalization]
  exact Category.comp_id v

/-- The direct normalized atlas pullback compares with its actual original source subgroup. -/
def evenNormalizedParameterSourceIso :
    CompatibleIso ((normalizedSubgroup n false).baseChange v) (H) :=
  (compatibleBaseChangeComp (cyclicHomUniversalSubgroup n)
    (cyclicHomNormalizedLocusInclusion n) v).symm.trans
      (cyclicHomUniversalSubgroupIsoOfFactorization n l f rfl (H) (hH))

/-- The original source comparison retains every independent auxiliary section. -/
theorem evenNormalizedParameterSourceIso_auxiliary (i : Labels 4) :
    pullSection v (evenNormalizedAuxiliaryMarking n i) ≫
      (evenNormalizedParameterSourceIso n v).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i := by
  change pullSection v (pullSection (cyclicHomNormalizedLocusInclusion n)
    (cyclicHomUniversalAuxiliaryMarking n i)) ≫
      ((compatibleBaseChangeComp (cyclicHomUniversalSubgroup n)
        (cyclicHomNormalizedLocusInclusion n) v).curve.inv.group ≫ _) = _
  rw [← Category.assoc, compatibleBaseChangeComp_inv_group_section]
  exact cyclicHomUniversalSubgroupIsoOfFactorization_auxiliary n l f rfl (H) (hH) i

/-- The original source comparison retains the specified normalized orbit generator. -/
theorem evenNormalizedParameterSourceIso_generator :
    pullSection v (evenNormalizedGenerator n) ≫
      (evenNormalizedParameterSourceIso n v).subgroup.hom =
        (H).orbitGenerator (cyclicHomSourceMarking n f) (hH) := by
  change pullSection v (pullSection (cyclicHomNormalizedLocusInclusion n)
    (cyclicHomUniversalGenerator n)) ≫
      ((compatibleBaseChangeComp (cyclicHomUniversalSubgroup n)
        (cyclicHomNormalizedLocusInclusion n) v).subgroup.inv ≫ _) = _
  rw [← Category.assoc, compatibleBaseChangeComp_inv_section]
  exact cyclicHomUniversalSubgroupIsoOfFactorization_generator n l f rfl (H) (hH)
    (orbitGenerator_cartier _ _ _) (orbitGenerator_curveMarking _ _ _)

end FLT.Mazur.CyclicCharacteristicAtlas
