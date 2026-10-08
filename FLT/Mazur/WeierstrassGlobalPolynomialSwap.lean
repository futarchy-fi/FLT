/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalAdditionGluing
public import FLT.Mazur.WeierstrassPolynomialAdditionSwap

/-!
# Global addition is commutative on every polynomial output-Z open

The explicit localized interchange identifies both restrictions of the
constructed global addition. This establishes the polynomial members of
the genuine input covers, without assumptions on reducedness or density.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Commutativity of the constructed global law on each polynomial output-Z domain. -/
theorem integralCurveAddition_swap_polynomial (b c : Bool) :
    projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralCurveProductChart W b c ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ =
      projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralCurveProductChart W b c ≫ integralCurveAddition W hΔ := by
  rw [← Category.assoc (integralCurveProductChart W b c), integralCurveProductChart_swap,
    Category.assoc, integralCurveProductChart_addition,
    ← Category.assoc, ← additionOutputSwap_inclusion, Category.assoc,
    integralInputAdditionToCurve_polynomial, ← Category.assoc, projectiveAdditionSpec_swap,
    integralCurveProductChart_addition, integralInputAdditionToCurve_polynomial]

/-- Any further scheme restriction of a polynomial domain retains commutativity. -/
theorem integralCurveAddition_swap_polynomial_restrict (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of
      (AdditionOutputOpen W (productChartCoordinate b) (productChartCoordinate c) 2))) :
    (f ≫ projectiveAdditionInclusion W
        (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralCurveProductChart W b c) ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ =
      (f ≫ projectiveAdditionInclusion W
        (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralCurveProductChart W b c) ≫ integralCurveAddition W hΔ := by
  simpa only [Category.assoc] using
    congrArg (fun g => f ≫ g) (integralCurveAddition_swap_polynomial W hΔ b c)

end FLT.Mazur.WeierstrassIntegralChart
