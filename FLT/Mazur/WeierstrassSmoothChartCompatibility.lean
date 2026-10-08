/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassPartialChartSmoothLocus

/-!
# Compatibility of the actual smooth addition charts

Equality on a common input scheme descends through the monomorphic smooth
inclusion. In particular the four restricted charts agree on their overlaps,
without a discriminant hypothesis or a reducedness assumption on the source.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The smooth restriction of a chart, viewed in the original affine input product. -/
def additionSmoothChartInclusion (i : AdditionChartIndex) :
    (additionSmoothInputOpen W i).toScheme ⟶ Spec (.of (AffineProduct W)) :=
  (additionSmoothInputOpen W i).ι ≫ additionChartInclusion W i

/-- Restricting a chart to smooth inputs preserves its open immersion. -/
instance additionSmoothChartInclusion_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (additionSmoothChartInclusion W i) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Smooth outputs agree whenever the original input morphisms agree. -/
theorem additionSmoothChart_commonScheme (i j : AdditionChartIndex)
    {X : Scheme.{u}} (f : X ⟶ (additionSmoothInputOpen W i).toScheme)
    (g : X ⟶ (additionSmoothInputOpen W j).toScheme)
    (h : f ≫ additionSmoothChartInclusion W i = g ≫ additionSmoothChartInclusion W j) :
    f ≫ additionSmoothChart W i = g ≫ additionSmoothChart W j := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, additionSmoothChart_inclusion]
  apply additionCurveChart_commonScheme W i j
    (f ≫ (additionSmoothInputOpen W i).ι) (g ≫ (additionSmoothInputOpen W j).ι)
  simpa only [additionSmoothChartInclusion, Category.assoc] using h

/-- The two smooth chart morphisms coincide on their actual scheme-theoretic overlap. -/
theorem additionSmoothChart_overlap (i j : AdditionChartIndex) :
    pullback.fst (additionSmoothChartInclusion W i) (additionSmoothChartInclusion W j) ≫
        additionSmoothChart W i =
      pullback.snd (additionSmoothChartInclusion W i) (additionSmoothChartInclusion W j) ≫
        additionSmoothChart W j :=
  additionSmoothChart_commonScheme W i j _ _ (pullback.condition)

end FLT.Mazur.WeierstrassIntegralChart
