/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothGoodReductionLocal

/-!
# The full smooth addition agrees with the good-reduction law

The actual smooth input covers descend the local comparisons to an equality
of morphisms on the categorical smooth-factor product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The good-reduction comparison holds on every mixed smooth input chart. -/
theorem smoothInputAddition_goodReduction_mixed (b c : Bool) (ha : b = false ∨ c = false) :
    smoothInputAddition W b c ≫ (integralSmoothOpen W).ι =
      smoothProductChartInput W b c ≫ integralCurveAddition W hΔ := by
  apply (smoothMixedCover W b c ha).hom_ext
  intro i
  cases i
  · exact smoothInputAddition_goodReduction_polynomial W hΔ b c
  · exact smoothInputAddition_goodReduction_affine W hΔ b c

/-- The three genuine Y/Y domains detect the good-reduction comparison. -/
theorem smoothInputAddition_goodReduction_y :
    smoothInputAddition W true true ≫ (integralSmoothOpen W).ι =
      smoothProductChartInput W true true ≫ integralCurveAddition W hΔ := by
  apply (smoothYCover W).hom_ext
  intro i
  cases i
  · exact smoothInputAddition_goodReduction_affine W hΔ true true
  · exact smoothInputAddition_goodReduction_polynomial W hΔ true true
  · exact smoothInputAddition_goodReduction_infinity W hΔ

/-- Each full smooth input chart computes the original good-reduction addition. -/
theorem smoothInputAddition_goodReduction (b c : Bool) :
    smoothInputAddition W b c ≫ (integralSmoothOpen W).ι =
      smoothProductChartInput W b c ≫ integralCurveAddition W hΔ := by
  cases b <;> cases c
  · exact smoothInputAddition_goodReduction_mixed W hΔ false false (.inl rfl)
  · exact smoothInputAddition_goodReduction_mixed W hΔ false true (.inl rfl)
  · exact smoothInputAddition_goodReduction_mixed W hΔ true false (.inr rfl)
  · exact smoothInputAddition_goodReduction_y W hΔ

/-- On the global smooth product open, both constructed addition maps agree. -/
@[reassoc] theorem smoothCurveAddition_goodReduction :
    smoothCurveAddition W ≫ (integralSmoothOpen W).ι =
      (smoothCurveProductOpen W).ι ≫ integralCurveAddition W hΔ := by
  apply (smoothCurveProductCover W).hom_ext
  rintro ⟨b, c⟩
  rw [← Category.assoc, smoothCurveProductCover_addition, Category.assoc,
    smoothInputAddition_goodReduction W hΔ, ← Category.assoc,
    smoothCurveProductCoverToChart_inputs, Category.assoc]

/-- The actual categorical smooth law is the restriction of the original integral law. -/
@[reassoc] theorem smoothFactorAddition_goodReduction :
    smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
      smoothFactorsInclusion W ≫ integralCurveAddition W hΔ := by
  rw [smoothFactorAddition, Category.assoc, smoothCurveAddition_goodReduction W hΔ,
    ← Category.assoc, smoothFactorsToProduct_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
