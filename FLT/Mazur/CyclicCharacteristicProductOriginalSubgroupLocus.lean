/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductSubgroupCharts
public import FLT.Mazur.CyclicCharacteristicAffineOriginalSubgroupLocus
public import FLT.Mazur.FiniteSubgroupComparisonRefinement

/-!
# The original global subgroup condition has the concrete affine charts

The closed locus of the constructed full universal comparison pulls back on
each comparison chart to the original affine subgroup parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "H" => productComparisonLeftSubgroup n b c
local notation "J" => productComparisonRightSubgroup n b c
local notation "e" => productUniversalComparison n b c
local notation "C" => Scheme.Cover.RelativeGluingData.cover (productComparisonGluing n b c)

/-- The subgroup condition for the actual full global universal comparison. -/
def productOriginalSubgroupLocus : Scheme := subgroupComparisonLocus H J e

/-- The subgroup condition keeps its original global parameter morphism. -/
def productOriginalSubgroupInclusion :
    productOriginalSubgroupLocus n b c ⟶ productComparisonScheme n b c :=
  subgroupComparisonLocusInclusion H J e

instance productOriginalSubgroupInclusion_closed :
    IsClosedImmersion (productOriginalSubgroupInclusion n b c) :=
  inferInstanceAs (IsClosedImmersion (subgroupComparisonLocusInclusion H J e))

variable (U : (normalizedProduct n b c).affineOpens)
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
local notation "a" => CompatibleIso.symm (productComparisonLeftSubgroupChart n b c U)
local notation "d" => CompatibleIso.symm (productComparisonRightSubgroupChart n b c U)

/-- The global comparison becomes the original affine one through compatible charts. -/
theorem productUniversalComparison_subgroupChart :
    affineUniversalComparison n b c L R =
      (a).curve ≪≫ (baseChangeFunctor ((C).f U)).mapIso e ≪≫ (d).curve.symm := by
  rw [productUniversalComparison_chart]
  simp only [CompatibleIso.symm, productComparisonLeftSubgroupChart_curve,
    productComparisonRightSubgroupChart_curve, Iso.symm_symm_eq, productUniversalChartComparison,
    Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Each concrete subgroup chart is the actual pullback of the global subgroup condition. -/
def productOriginalSubgroupChartIso : affineSubgroupScheme n b c L R ≅
    pullback ((C).f U) (productOriginalSubgroupInclusion n b c) :=
  affineOriginalSubgroupLocusIso n b c L R ≪≫
    subgroupComparisonRefinementIsoOfEq H J e ((C).f U) a d
      (affineUniversalComparison n b c L R) (productUniversalComparison_subgroupChart n b c U)

/-- The identification preserves the concrete chart's closed parameter immersion. -/
@[reassoc] theorem productOriginalSubgroupChartIso_fst :
    (productOriginalSubgroupChartIso n b c U).hom ≫ pullback.fst _ _ =
      affineSubgroupInclusion n b c L R := by
  change ((affineOriginalSubgroupLocusIso n b c L R).hom ≫
    (subgroupComparisonRefinementIsoOfEq H J e ((C).f U) a d
      (affineUniversalComparison n b c L R)
      (productUniversalComparison_subgroupChart n b c U)).hom) ≫
        pullback.fst _ (subgroupComparisonLocusInclusion H J e) = _
  rw [Category.assoc, subgroupComparisonRefinementIsoOfEq_fst]
  exact affineOriginalSubgroupLocusIso_inclusion n b c L R

end FLT.Mazur.CyclicCharacteristicAtlas
