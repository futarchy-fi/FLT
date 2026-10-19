/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductUniversalRefinement
public import FLT.Mazur.GeneralizedCurveNaturalIsoGluing

/-!
# The full universal comparison over the glued product parameter scheme

The actual affine universal comparisons glue to an isomorphism between the
original global families. Restriction recovers every full chart comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "C" => Scheme.Cover.RelativeGluingData.cover (productComparisonGluing n b c)

/-- The actual full universal comparison on the glued parameter scheme. -/
def productUniversalComparison :
    productComparisonLeftCurve n b c ≅ productComparisonRightCurve n b c :=
  glueIsoOfRefinement C (productUniversalChartComparison n b c)
    (fun h ↦ productUniversalChartComparison_refine n b c h)

/-- Every chart recovers its prescribed full universal comparison. -/
theorem productUniversalComparison_chart (U : (normalizedProduct n b c).affineOpens) :
    (baseChangeFunctor ((C).f U)).mapIso (productUniversalComparison n b c) =
      productUniversalChartComparison n b c U :=
  glueIsoOfRefinement_map C (productUniversalChartComparison n b c)
    (fun h ↦ productUniversalChartComparison_refine n b c h) U

/-- The original full families admit exactly one comparison with the prescribed charts. -/
theorem productUniversalComparison_unique :
    ∃! e : productComparisonLeftCurve n b c ≅ productComparisonRightCurve n b c,
      ∀ U, (baseChangeFunctor ((C).f U)).mapIso e = productUniversalChartComparison n b c U :=
  glueIsoOfRefinement_unique C (productUniversalChartComparison n b c)
    (fun h ↦ productUniversalChartComparison_refine n b c h)

end FLT.Mazur.CyclicCharacteristicAtlas
