/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothOriginalAffine
public import FLT.Mazur.WeierstrassGlobalInfinitySwap

/-!
# Good-reduction comparison on the smooth addition domains

The affine, polynomial and infinity formulas of the full smooth law agree
with the original good-reduction addition on their actual input domains.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The smooth affine law is the restriction of good-reduction addition. -/
theorem smoothAffineAddition_goodReduction :
    smoothAffineAddition W ≫ (integralSmoothOpen W).ι =
      (smoothAffineInputOpen W).ι ≫ affineAdditionToCurve W hΔ := by
  rw [smoothAffineAddition_partial, affinePartialAddition_goodReduction,
    ← Category.assoc, smoothAffineInputToDomain_inclusion]

/-- Transported affine smooth domains retain the good-reduction addition. -/
theorem smoothInputAddition_goodReduction_affine (b c : Bool) :
    smoothAffineOverlapToChart W b c ≫ smoothInputAddition W b c ≫
        (integralSmoothOpen W).ι =
      smoothAffineOverlapToChart W b c ≫ smoothProductChartInput W b c ≫
        integralCurveAddition W hΔ := by
  rw [smoothInputAddition_affine_assoc, smoothAffineOverlapAddition, Category.assoc,
    smoothAffineAddition_goodReduction W hΔ, ← integralCurveProductChart_affine_addition W hΔ]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ integralCurveAddition W hΔ)
    (smoothAffineOverlapToInputs_global W b c)

/-- Polynomial smooth domains retain the good-reduction addition. -/
theorem smoothInputAddition_goodReduction_polynomial (b c : Bool) :
    smoothPolynomialToInputs W b c 2 ≫ smoothInputAddition W b c ≫
        (integralSmoothOpen W).ι =
      smoothPolynomialToInputs W b c 2 ≫ smoothProductChartInput W b c ≫
        integralCurveAddition W hΔ := by
  rw [smoothInputAddition_polynomial_assoc, polynomialSmoothChart_inclusion,
    smoothProductChartInput, Category.assoc, smoothPolynomialToInputs_inclusion_assoc,
    smoothPolynomialInput, Category.assoc,
    integralCurveProductChart_addition, integralInputAdditionToCurve_polynomial]

/-- The infinity smooth domain retains the good-reduction addition. -/
theorem smoothInputAddition_goodReduction_infinity :
    smoothInfinityToInputs W ≫ smoothInputAddition W true true ≫
        (integralSmoothOpen W).ι =
      smoothInfinityToInputs W ≫ smoothProductChartInput W true true ≫
        integralCurveAddition W hΔ := by
  rw [smoothInputAddition_infinity_assoc, infinitySmoothChart_inclusion,
    smoothProductChartInput, Category.assoc, smoothInfinityToInputs_inclusion_assoc,
    smoothInfinityInput, Category.assoc, integralCurveAddition_infinity]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
