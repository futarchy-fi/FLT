/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianTestEquiv
public import FLT.Mazur.CyclicCharacteristicProductComparisonGluing
public import FLT.Mazur.CyclicCharacteristicProductSubgroupGluing

/-!
# Arbitrary scheme tests on charts of the glued comparison schemes

The actual cartesian chart squares recover tests without restricting the
test scheme to affine, reduced, or etale schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
  (U : (normalizedProduct n b c).affineOpens) {T : Scheme} (a : T ⟶ U.1.toScheme)

/-- Tests of the global comparison scheme over an open recover the original comparison chart. -/
def productComparisonChartTestEquiv :
    {k : T ⟶ productOpenComparison n b c U //
      k ≫ productOpenComparisonStructure n b c U = a} ≃
    {k : T ⟶ productComparisonScheme n b c //
      k ≫ productComparisonStructure n b c = a ≫ U.1.ι} :=
  cartesianTestEquiv (productComparisonChart_isPullback n b c U) a

/-- Tests of the global subgroup scheme over an open recover the original closed chart. -/
def productSubgroupChartTestEquiv :
    {k : T ⟶ productOpenSubgroup n b c U //
      k ≫ productOpenSubgroupStructure n b c U = a} ≃
    {k : T ⟶ productSubgroupScheme n b c //
      k ≫ productSubgroupStructure n b c = a ≫ U.1.ι} :=
  cartesianTestEquiv (productSubgroupChart_isPullback n b c U) a

/-- Chart recovery retains the actual global subgroup-test morphism. -/
theorem productSubgroupChartTestEquiv_apply
    (k : {k : T ⟶ productOpenSubgroup n b c U //
      k ≫ productOpenSubgroupStructure n b c U = a}) :
    (productSubgroupChartTestEquiv n b c U a k).val =
      k.val ≫ (productSubgroupCover n b c).f U := rfl

end FLT.Mazur.CyclicCharacteristicAtlas
