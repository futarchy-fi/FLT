/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointArrowRecovery
public import FLT.Mazur.CyclicCharacteristicIntegerSourceFunctions

/-!
# Full comparison invariance of the assembled characteristic function

The assembled function respects all original comparison arrows on arbitrary
scheme tests. The two-component source cover detects the full relation
equation, including same-chart and cross-characteristic arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The actual two-component source cover, regarded as an fppf family. -/
def integerSourceFppfCover :
    Scheme.Cover.{0} Scheme.fppfPrecoverage (integerSourceOpen n b).toScheme where
  __ := (integerSourceCover n b).toPreZeroHypercover
  mem₀ := Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (integerSourceCover n b).mem₀

/-- Original global arrows between source charts preserve the assembled function. -/
theorem integerSourceFunction_chart_test (s : chartResidualSections n (!b))
    {T : Scheme} (c d : Bool)
    (g : T ⟶ integerSourceChart n b c) (k : T ⟶ integerSourceChart n b d)
    (a : T ⟶ disjointComparisonArrows n)
    (hs : a ≫ disjointComparisonSource n =
      g ≫ integerSourceChartMap n b c ≫ (integerSourceOpen n b).ι)
    (ht : a ≫ disjointComparisonTarget n =
      k ≫ integerSourceChartMap n b d ≫ (integerSourceOpen n b).ι) :
    g.appTop ((integerSourceChartMap n b c).appTop (integerSourceFunction n b s)) =
      k.appTop ((integerSourceChartMap n b d).appTop (integerSourceFunction n b s)) := by
  cases c <;> cases d <;> dsimp only [integerSourceChart, integerSourceChartMap] at *
  · rw [integerSourceFunction_selected]
    have h := disjointComparison_unmarkedRelated n (!b) (!b) g k a
      (by simpa only [integerSourceChartMap, selectedToIntegerSource_comp] using hs)
      (by simpa only [integerSourceChartMap, selectedToIntegerSource_comp] using ht)
    have he := congrArg (functionEquiv T)
      (residual_invariant_on_test n b ((functionEquiv _).symm s.val)
        (residualFunctionMorphism_invariant n b s) g k h)
    simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using he
  · rw [integerSourceFunction_selected, integerSourceFunction_opposite]
    have h := disjointComparison_unmarkedRelated n (!b) b g
      (k ≫ (transitionOpen n b).ι) a
      (by simpa only [integerSourceChartMap, selectedToIntegerSource_comp] using hs)
      (by simpa only [integerSourceChartMap, oppositeToIntegerSource_comp,
        Category.assoc] using ht)
    exact (residualSectionReconstruction_on_test n b s k g
      (UnmarkedRelated.symm n h)).symm
  · rw [integerSourceFunction_selected, integerSourceFunction_opposite]
    have h := disjointComparison_unmarkedRelated n b (!b)
      (g ≫ (transitionOpen n b).ι) k a
      (by simpa only [integerSourceChartMap, oppositeToIntegerSource_comp,
        Category.assoc] using hs)
      (by simpa only [integerSourceChartMap, selectedToIntegerSource_comp] using ht)
    exact residualSectionReconstruction_on_test n b s g k h
  · rw [integerSourceFunction_opposite]
    have h := disjointComparison_unmarkedRelated n b b
      (g ≫ (transitionOpen n b).ι) (k ≫ (transitionOpen n b).ι) a
      (by simpa only [integerSourceChartMap, oppositeToIntegerSource_comp,
        Category.assoc] using hs)
      (by simpa only [integerSourceChartMap, oppositeToIntegerSource_comp,
        Category.assoc] using ht)
    exact residualSectionReconstruction_invariant n b s g k h

/-- Every original comparison with both endpoints in the source open preserves the function. -/
theorem integerSourceFunction_relation (s : chartResidualSections n (!b))
    {D : Scheme} (p q : D ⟶ (integerSourceOpen n b).toScheme)
    (a : D ⟶ disjointComparisonArrows n)
    (hs : a ≫ disjointComparisonSource n = p ≫ (integerSourceOpen n b).ι)
    (ht : a ≫ disjointComparisonTarget n = q ≫ (integerSourceOpen n b).ι) :
    p.appTop (integerSourceFunction n b s) = q.appTop (integerSourceFunction n b s) := by
  apply SchemeFppfFamily.relation_eq_of_chart_tests (integerSourceFppfCover n b)
  intro T c d g k w hp hq
  apply integerSourceFunction_chart_test n b s c d g k (w ≫ a)
  · rw [Category.assoc, hs, ← Category.assoc, hp, Category.assoc]
    rfl
  · rw [Category.assoc, ht, ← Category.assoc, hq, Category.assoc]
    rfl

end FLT.Mazur.CyclicCharacteristicOrbit
