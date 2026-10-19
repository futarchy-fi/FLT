/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointArrowRecovery
public import FLT.Mazur.CyclicCharacteristicAffineSourceFunctions

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
  (j : (invariantAffineCover n (!b)).I₀)

/-- The actual two-component source cover, regarded as an fppf family. -/
def affineSourceFppfCover :
    Scheme.Cover.{0} Scheme.fppfPrecoverage (affineSourceOpen n b j).toScheme where
  __ := (affineSourceCover n b j).toPreZeroHypercover
  mem₀ := Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (affineSourceCover n b j).mem₀

/-- Original global arrows between source charts preserve the assembled function. -/
theorem affineSourceFunction_chart_test (s : affineResidualSections n ⟨!b, j⟩)
    {T : Scheme} (c d : Bool)
    (g : T ⟶ affineSourceChart n b j c) (k : T ⟶ affineSourceChart n b j d)
    (a : T ⟶ disjointComparisonArrows n)
    (hs : a ≫ disjointComparisonSource n =
      g ≫ affineSourceChartMap n b j c ≫ (affineSourceOpen n b j).ι)
    (ht : a ≫ disjointComparisonTarget n =
      k ≫ affineSourceChartMap n b j d ≫ (affineSourceOpen n b j).ι) :
    g.appTop ((affineSourceChartMap n b j c).appTop (affineSourceFunction n b j s)) =
      k.appTop ((affineSourceChartMap n b j d).appTop (affineSourceFunction n b j s)) := by
  cases c <;> cases d <;> dsimp only [affineSourceChart, affineSourceChartMap] at *
  · rw [affineSourceFunction_selected]
    have h := disjointComparison_unmarkedRelated n (!b) (!b)
      (g ≫ invariantAffineInclusion n ⟨!b, j⟩)
      (k ≫ invariantAffineInclusion n ⟨!b, j⟩) a
      (by simpa only [affineSourceChartMap, selectedToAffineSource_comp,
        Category.assoc] using hs)
      (by simpa only [affineSourceChartMap, selectedToAffineSource_comp,
        Category.assoc] using ht)
    have he := congrArg (functionEquiv T)
      (affineResidual_invariant_on_test n ⟨!b, j⟩ ((functionEquiv _).symm s.val)
        (affineResidualFunctionMorphism_invariant n b j s) g k h)
    simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using he
  · rw [affineSourceFunction_selected, affineSourceFunction_opposite]
    have h := disjointComparison_unmarkedRelated n (!b) b
      (g ≫ invariantAffineInclusion n ⟨!b, j⟩)
      (k ≫ (affineOppositeOpen n b j).ι) a
      (by simpa only [affineSourceChartMap, selectedToAffineSource_comp,
        Category.assoc] using hs)
      (by simpa only [affineSourceChartMap, oppositeToAffineSource_comp,
        Category.assoc] using ht)
    exact (affineSectionReconstruction_on_test n b j s k g
      (UnmarkedRelated.symm n h)).symm
  · rw [affineSourceFunction_selected, affineSourceFunction_opposite]
    have h := disjointComparison_unmarkedRelated n b (!b)
      (g ≫ (affineOppositeOpen n b j).ι)
      (k ≫ invariantAffineInclusion n ⟨!b, j⟩) a
      (by simpa only [affineSourceChartMap, oppositeToAffineSource_comp,
        Category.assoc] using hs)
      (by simpa only [affineSourceChartMap, selectedToAffineSource_comp,
        Category.assoc] using ht)
    exact affineSectionReconstruction_on_test n b j s g k h
  · rw [affineSourceFunction_opposite]
    have h := disjointComparison_unmarkedRelated n b b
      (g ≫ (affineOppositeOpen n b j).ι) (k ≫ (affineOppositeOpen n b j).ι) a
      (by simpa only [affineSourceChartMap, oppositeToAffineSource_comp,
        Category.assoc] using hs)
      (by simpa only [affineSourceChartMap, oppositeToAffineSource_comp,
        Category.assoc] using ht)
    exact affineSectionReconstruction_invariant n b j s g k h

/-- Every original comparison with both endpoints in the source open preserves the function. -/
theorem affineSourceFunction_relation (s : affineResidualSections n ⟨!b, j⟩)
    {D : Scheme} (p q : D ⟶ (affineSourceOpen n b j).toScheme)
    (a : D ⟶ disjointComparisonArrows n)
    (hs : a ≫ disjointComparisonSource n = p ≫ (affineSourceOpen n b j).ι)
    (ht : a ≫ disjointComparisonTarget n = q ≫ (affineSourceOpen n b j).ι) :
    p.appTop (affineSourceFunction n b j s) = q.appTop (affineSourceFunction n b j s) := by
  apply SchemeFppfFamily.relation_eq_of_chart_tests (affineSourceFppfCover n b j)
  intro T c d g k w hp hq
  apply affineSourceFunction_chart_test n b j s c d g k (w ≫ a)
  · rw [Category.assoc, hs, ← Category.assoc, hp, Category.assoc]
    rfl
  · rw [Category.assoc, ht, ← Category.assoc, hq, Category.assoc]
    rfl

end FLT.Mazur.CyclicCharacteristicOrbit
