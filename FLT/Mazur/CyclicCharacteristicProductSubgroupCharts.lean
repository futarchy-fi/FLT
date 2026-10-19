/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductUniversalComparison
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq

/-!
# Original subgroup families on the global comparison scheme

The global families retain their original finite subgroups. Their chart
identifications extend the full curve identifications compatibly.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "s" => productComparisonStructure n b c
local notation "C" => Scheme.Cover.RelativeGluingData.cover (productComparisonGluing n b c)

/-- The original left finite subgroup on the entire parameter scheme. -/
def productComparisonLeftSubgroup : (productComparisonLeftCurve n b c).FiniteSubgroup n :=
  (normalizedSubgroup n b).baseChange (s ≫ prod.fst)

/-- The original right finite subgroup on the entire parameter scheme. -/
def productComparisonRightSubgroup : (productComparisonRightCurve n b c).FiniteSubgroup n :=
  (normalizedSubgroup n c).baseChange (s ≫ prod.snd)

variable (U : (normalizedProduct n b c).affineOpens)
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
local notation "t" => affineComparisonStructure n b c L R

/-- The full left chart identification preserves the original finite subgroup. -/
def productComparisonLeftSubgroupChart :
    CompatibleIso ((productComparisonLeftSubgroup n b c).baseChange ((C).f U))
      (((normalizedSubgroup n b).baseChange L).baseChange t) :=
  (compatibleBaseChangeComp (normalizedSubgroup n b) (s ≫ prod.fst) ((C).f U)).symm.trans
    (compatibleBaseChangeCompEq (normalizedSubgroup n b) L t ((C).f U ≫ (s ≫ prod.fst))
      (productComparisonLeftChart_base n b c U))

/-- The full right chart identification preserves the original finite subgroup. -/
def productComparisonRightSubgroupChart :
    CompatibleIso ((productComparisonRightSubgroup n b c).baseChange ((C).f U))
      (((normalizedSubgroup n c).baseChange R).baseChange t) :=
  (compatibleBaseChangeComp (normalizedSubgroup n c) (s ≫ prod.snd) ((C).f U)).symm.trans
    (compatibleBaseChangeCompEq (normalizedSubgroup n c) R t ((C).f U ≫ (s ≫ prod.snd))
      (productComparisonRightChart_base n b c U))

/-- The left compatible chart uses the previously specified full curve transport. -/
theorem productComparisonLeftSubgroupChart_curve :
    (productComparisonLeftSubgroupChart n b c U).curve =
      productComparisonLeftChartIso n b c U := by
  simp only [productComparisonLeftSubgroupChart, CompatibleIso.trans, CompatibleIso.symm,
    compatibleBaseChangeCompEq_curve]
  rfl

/-- The right compatible chart uses the previously specified full curve transport. -/
theorem productComparisonRightSubgroupChart_curve :
    (productComparisonRightSubgroupChart n b c U).curve =
      productComparisonRightChartIso n b c U := by
  simp only [productComparisonRightSubgroupChart, CompatibleIso.trans, CompatibleIso.symm,
    compatibleBaseChangeCompEq_curve]
  rfl

end FLT.Mazur.CyclicCharacteristicAtlas
