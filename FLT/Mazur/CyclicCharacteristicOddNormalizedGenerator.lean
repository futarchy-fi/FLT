/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedSubgroup
public import FLT.Mazur.OddWeierstrassCyclicHomUniversalPrescribedGenerator
public import FLT.Mazur.CompatibleSubgroupGeneratorBaseChange

/-!
# The actual odd normalized subgroup retains its chosen source generator

Compare the direct pullback of the characteristic atlas subgroup with the
normalized source construction. The comparison identifies the pullback of
the universal label-one generator with the chosen normalized orbit generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open OddWeierstrassParameter GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The specified Cartier generator on the actual odd normalized chart. -/
def oddNormalizedGenerator : 𝟙_ (Over (normalizedLocus n true)) ⟶
    (normalizedSubgroup n true).carrier :=
  pullSection (cyclicHomNormalizedLocusInclusion n) (cyclicHomUniversalGenerator n)

/-- The specified normalized generator retains the full Cartier orbit divisor. -/
theorem oddNormalizedGenerator_cartier :
    (normalizedSubgroup n true).IsCartierGenerator (oddNormalizedGenerator n) :=
  (cyclicHomUniversalGenerator_cartier n).baseChange _ (cyclicHomNormalizedLocusInclusion n)

variable {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)
local notation "q" => cyclicHomNormalizedLocusPoint n f h
local notation "fN" => cyclicHomNormalizedPoint n f
local notation "hN" => cyclicHomNormalization_equation n f h
local notation "HN" => cyclicHomSubgroup n fN hN

/-- The direct actual chart subgroup compares with the reconstructed normalized source. -/
def oddNormalizedSourceIso :
    CompatibleIso ((normalizedSubgroup n true).baseChange q) (HN) :=
  (compatibleBaseChangeComp (cyclicHomUniversalSubgroup n)
    (cyclicHomNormalizedLocusInclusion n) q).symm.trans
      (cyclicHomUniversalSubgroupIsoOfFactorization n
        (q ≫ cyclicHomNormalizedLocusInclusion n) fN
        ((Category.assoc _ _ _).trans (cyclicHomNormalizedLocusPoint_parameter n f h))
        (HN) (cyclicHomSubgroup_ideal n fN hN))

/-- This full comparison preserves the chosen normalized generator itself. -/
theorem oddNormalizedSourceIso_generator :
    pullSection q (oddNormalizedGenerator n) ≫ (oddNormalizedSourceIso n f h).subgroup.hom =
      (HN).orbitGenerator (cyclicHomSourceMarking n fN) (cyclicHomSubgroup_ideal n fN hN) := by
  change pullSection q (pullSection (cyclicHomNormalizedLocusInclusion n)
    (cyclicHomUniversalGenerator n)) ≫
      ((compatibleBaseChangeComp (cyclicHomUniversalSubgroup n)
        (cyclicHomNormalizedLocusInclusion n) q).subgroup.inv ≫ _) = _
  rw [← Category.assoc, compatibleBaseChangeComp_inv_section]
  exact cyclicHomUniversalSubgroupIsoOfFactorization_generator n _ _ _ (HN)
    (cyclicHomSubgroup_ideal n fN hN) (orbitGenerator_cartier _ _ _)
    (orbitGenerator_curveMarking _ _ _)

end FLT.Mazur.CyclicCharacteristicAtlas
