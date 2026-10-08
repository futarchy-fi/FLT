/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineAdditionSwapDescent
public import FLT.Mazur.WeierstrassGlobalPolynomialSwap

/-!
# Commutativity of global addition whenever an input is in the affine chart

The affine comparison identifies both restrictions of the global addition.
Together with polynomial symmetry, the actual two-member mixed input cover
extends commutativity to all three input products with an affine factor.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Global addition restricts to the already descended affine addition morphism. -/
theorem integralCurveProductChart_affine_addition :
    integralCurveProductChart W false false ≫ integralCurveAddition W hΔ =
      affineAdditionToCurve W hΔ := by
  rw [integralCurveProductChart_addition]
  simpa only [Category.id_comp] using
    integralInputAdditionToCurve_commonAffine W hΔ false false (𝟙 _) (𝟙 _) rfl

/-- Global addition is commutative on the complete affine input product. -/
theorem integralCurveAddition_swap_affine :
    integralCurveProductChart W false false ≫ integralCurveSwap W ≫
        integralCurveAddition W hΔ =
      integralCurveProductChart W false false ≫ integralCurveAddition W hΔ := by
  rw [← Category.assoc, integralCurveProductChart_swap, Category.assoc,
    integralCurveProductChart_affine_addition]
  exact affineAdditionToCurve_swap W hΔ

/-- Every scheme mapping into the affine input product retains commutativity. -/
theorem integralCurveAddition_swap_commonAffine {X : Scheme.{u}}
    (f : X ⟶ integralCurveProduct W) (g : X ⟶ Spec (.of (AffineProduct W)))
    (h : f = g ≫ integralCurveProductChart W false false) :
    f ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ =
      f ≫ integralCurveAddition W hΔ := by
  rw [h]
  simpa only [Category.assoc] using
    congrArg (fun t => g ≫ t) (integralCurveAddition_swap_affine W hΔ)

/-- Every affine overlap in the four input products retains commutativity. -/
theorem integralCurveAddition_swap_affineOverlap (b c : Bool) :
    Spec.map (CommRingCat.ofHom (productOverlapRestriction W
        (productChartCoordinate b) (productChartCoordinate c) 2 2).toRingHom) ≫
      integralCurveProductChart W b c ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ =
    Spec.map (CommRingCat.ofHom (productOverlapRestriction W
        (productChartCoordinate b) (productChartCoordinate c) 2 2).toRingHom) ≫
      integralCurveProductChart W b c ≫ integralCurveAddition W hΔ := by
  have h : Spec.map (CommRingCat.ofHom (productOverlapRestriction W
        (productChartCoordinate b) (productChartCoordinate c) 2 2).toRingHom) ≫
      integralCurveProductChart W b c =
    affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) ≫
      integralCurveProductChart W false false :=
    integralProductOverlap_condition W b c false false
  simpa only [Category.assoc] using
    integralCurveAddition_swap_commonAffine W hΔ _ _ h

/-- Commutativity holds on every input chart with an affine factor. -/
theorem integralCurveAddition_swap_mixed (b c : Bool)
    (ha : productChartCoordinate b = 2 ∨ productChartCoordinate c = 2) :
    integralCurveProductChart W b c ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ =
      integralCurveProductChart W b c ≫ integralCurveAddition W hΔ := by
  have hb : productChartCoordinate b = 1 ∨ productChartCoordinate b = 2 := by
    cases b <;> simp [productChartCoordinate]
  have hc : productChartCoordinate c = 1 ∨ productChartCoordinate c = 2 := by
    cases c <;> simp [productChartCoordinate]
  apply (mixedProductOpenCover W (productChartCoordinate b) (productChartCoordinate c)
    hb hc ha).hom_ext
  intro i
  cases i
  · exact integralCurveAddition_swap_polynomial W hΔ b c
  · exact integralCurveAddition_swap_affineOverlap W hΔ b c

end FLT.Mazur.WeierstrassIntegralChart
