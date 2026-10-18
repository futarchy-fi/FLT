/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenNormalizedGenerator
public import FLT.Mazur.CyclicHomUniversalAuxiliaryMarking
public import FLT.Mazur.CompatibleSubgroupGroupSectionComposition

/-!
# Auxiliary markings on the actual even normalized chart

Restrict the universal auxiliary frame to the normalized chart. The full
comparison with a reconstructed normalized source preserves every label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open UniversalWeierstrass GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual auxiliary frame restricted to the even normalized chart. -/
def evenNormalizedAuxiliaryMarking (i : Labels 4) :
    𝟙_ (Over (normalizedLocus n false)) ⟶ (normalizedCurve n false).group :=
  pullSection (cyclicHomNormalizedLocusInclusion n) (cyclicHomUniversalAuxiliaryMarking n i)

variable {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)
local notation "q" => cyclicHomNormalizedLocusPoint n f h
local notation "fN" => cyclicHomNormalizedPoint n f
local notation "hN" => cyclicHomNormalization_equation n f h
local notation "HN" => cyclicHomSubgroup n fN hN

/-- The direct chart comparison retains the independent normalized auxiliary labels. -/
theorem evenNormalizedSourceIso_auxiliary (i : Labels 4) :
    pullSection q (evenNormalizedAuxiliaryMarking n i) ≫
      (evenNormalizedSourceIso n f h).curve.hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fN) i := by
  change pullSection q (pullSection (cyclicHomNormalizedLocusInclusion n)
    (cyclicHomUniversalAuxiliaryMarking n i)) ≫
      ((compatibleBaseChangeComp (cyclicHomUniversalSubgroup n)
        (cyclicHomNormalizedLocusInclusion n) q).curve.inv.group ≫ _) = _
  rw [← Category.assoc, compatibleBaseChangeComp_inv_group_section]
  exact cyclicHomUniversalSubgroupIsoOfFactorization_auxiliary n _ _ _ (HN)
    (cyclicHomSubgroup_ideal n fN hN) i

end FLT.Mazur.CyclicCharacteristicAtlas
