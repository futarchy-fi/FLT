/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingTestCubicChart

/-!
# A full pointed coefficient presentation on arbitrary test schemes

The actual coefficient cubics cover the pulled-back global cubic. Their
infinity sections agree with the original marking image, and their whole
curve maps are the categorical restrictions of the original global map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (g : T ⟶ S)

/-- Actual coefficient equations cover the entire cubic on every unrestricted test. -/
def smoothMarkingTestCubicCover : (smoothMarkingPulledCubic E s g).OpenCover where
  I₀ := SmoothMarkingTestChart E s g
  X c := integralCurve (smoothMarkingTestChartEquation E s g c)
  f c := smoothMarkingTestChartMap E s g c
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨c, hc, _⟩ := exists_smoothMarkingTestChart E s g
      (show smoothMarkingPulledBase E s g x ∈ (⊤ : T.Opens) from trivial)
    have hx : x ∈ Set.range (smoothMarkingTestChartMap E s g c) := by
      rw [smoothMarkingTestChartMap_range]
      exact hc
    obtain ⟨y, hy⟩ := hx
    exact ⟨c, y, hy⟩

variable (c : SmoothMarkingTestChart E s g)

/-- Every coefficient chart has the original infinity section on its actual base open. -/
@[reassoc] theorem smoothMarkingTestChartMap_zero :
    affineIntegralZero (smoothMarkingTestChartEquation E s g c) ≫
      smoothMarkingTestChartMap E s g c = c.base.1.ι ≫ smoothMarkingPulledZero E s g := by
  apply Limits.pullback.hom_ext
  · change _ ≫ smoothMarkingPulledProjection E s g =
      (c.base.1.ι ≫ smoothMarkingPulledZero E s g) ≫ smoothMarkingPulledProjection E s g
    rw [Category.assoc, smoothMarkingTestChartMap_projection, ← Category.assoc]
    change (affineIntegralZero ((smoothMarkingAffineEquation E s c.original).map
      c.map.appTop.hom) ≫ affineIntegralCoefficient
        (smoothMarkingAffineEquation E s c.original) c.map) ≫ _ = _
    rw [affineIntegralCoefficient_zero, Category.assoc]
    change c.map ≫ smoothMarkingAffineZero E s c.original ≫
      smoothMarkingGluedChart E s c.original = _
    rw [smoothMarkingAffineZero_chart, ← Category.assoc, c.fac,
      Category.assoc, Category.assoc, smoothMarkingPulledZero_projection]
  · change _ ≫ smoothMarkingPulledBase E s g =
      (c.base.1.ι ≫ smoothMarkingPulledZero E s g) ≫ smoothMarkingPulledBase E s g
    rw [Category.assoc, smoothMarkingTestChartMap_over, ← Category.assoc,
      affineIntegralZero_over, Category.id_comp, Category.assoc,
      smoothMarkingPulledZero_over, Category.comp_id]

/-- The actual restricted whole original family maps to its concrete coefficient equation. -/
def smoothMarkingTestChartCurveMap : ((E.baseChange g).baseChange c.base.1.ι).curve.left ⟶
    integralCurve (smoothMarkingTestChartEquation E s g c) :=
  (smoothMarkingTestChart_isPullback E s g c).lift
    (Limits.pullback.fst (E.baseChange g).curve.hom c.base.1.ι ≫
      smoothMarkingToPulledCubic E s g)
    (Limits.pullback.snd (E.baseChange g).curve.hom c.base.1.ι)
    (by rw [Category.assoc, smoothMarkingToPulledCubic_over];
        exact Limits.pullback.condition)

/-- The local coefficient map recovers the whole original global map after chart inclusion. -/
@[reassoc] theorem smoothMarkingTestChartCurveMap_chart :
    smoothMarkingTestChartCurveMap E s g c ≫ smoothMarkingTestChartMap E s g c =
      Limits.pullback.fst (E.baseChange g).curve.hom c.base.1.ι ≫
        smoothMarkingToPulledCubic E s g := IsPullback.lift_fst _ _ _ _

/-- The original local whole-curve map retains its original affine test base. -/
@[reassoc] theorem smoothMarkingTestChartCurveMap_over :
    smoothMarkingTestChartCurveMap E s g c ≫
      affineIntegralStructure (smoothMarkingTestChartEquation E s g c) =
        ((E.baseChange g).baseChange c.base.1.ι).curve.hom := IsPullback.lift_snd _ _ _ _

/-- The actual marking on each restricted original family is the equation's infinity section. -/
@[reassoc] theorem smoothMarkingTestChartCurveMap_marking :
    (GroupSectionBaseChange.pullSection c.base.1.ι (GroupSectionBaseChange.pullSection g s) ≫
      ((E.baseChange g).baseChange c.base.1.ι).inclusion).left ≫
        smoothMarkingTestChartCurveMap E s g c =
          affineIntegralZero (U := c.base.1.toScheme)
            (smoothMarkingTestChartEquation E s g c) := by
  apply (cancel_mono (smoothMarkingTestChartMap E s g c)).mp
  rw [Category.assoc, smoothMarkingTestChartCurveMap_chart,
    ← (E.baseChange g).pullSection_smoothMarking c.base.1.ι
      (GroupSectionBaseChange.pullSection g s),
    ← Category.assoc, GroupSectionBaseChange.section_fst,
    Category.assoc, smoothMarkingToPulledCubic_marking, smoothMarkingTestChartMap_zero]

/-- These are categorical restrictions of the actual global whole-family morphism. -/
theorem smoothMarkingTestChartCurveMap_isPullback :
    IsPullback (smoothMarkingTestChartCurveMap E s g c)
      (Limits.pullback.fst (E.baseChange g).curve.hom c.base.1.ι)
      (smoothMarkingTestChartMap E s g c) (smoothMarkingToPulledCubic E s g) := by
  have H : IsPullback
      (smoothMarkingTestChartCurveMap E s g c ≫
        affineIntegralStructure (smoothMarkingTestChartEquation E s g c))
      (Limits.pullback.fst (E.baseChange g).curve.hom c.base.1.ι) c.base.1.ι
      (smoothMarkingToPulledCubic E s g ≫ smoothMarkingPulledBase E s g) := by
    rw [smoothMarkingTestChartCurveMap_over, smoothMarkingToPulledCubic_over]
    exact (IsPullback.of_hasPullback (E.baseChange g).curve.hom c.base.1.ι).flip
  exact H.of_right (smoothMarkingTestChartCurveMap_chart E s g c)
    (smoothMarkingTestChart_isPullback E s g c).flip

/-- The actual original whole-curve maps to the coefficient equations are proper. -/
instance smoothMarkingTestChartCurveMap_isProper :
    IsProper (smoothMarkingTestChartCurveMap E s g c) :=
  MorphismProperty.of_isPullback (smoothMarkingTestChartCurveMap_isPullback E s g c).flip
    inferInstance

end FLT.Mazur.GeneralizedEllipticCurve
