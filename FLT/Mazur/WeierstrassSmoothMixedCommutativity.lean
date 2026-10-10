/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineCommutativity
public import FLT.Mazur.WeierstrassPolynomialAdditionSwap

/-!
# Smooth commutativity on the polynomial domains and mixed charts

Polynomial interchange respects normalized output. Together with the smooth
affine calculation, this proves symmetry on every mixed input chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The full smooth law is symmetric on every original polynomial presentation. -/
theorem smoothCurveAddition_swap_polynomial (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate b) (productChartCoordinate c) 2)))
    (h : f ≫ (smoothCurveProductOpen W).ι =
      g ≫ projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralCurveProductChart W b c) :
    f ≫ smoothProductSwap W ≫ smoothCurveAddition W = f ≫ smoothCurveAddition W := by
  let s := Spec.map (CommRingCat.ofHom (additionOutputSwap W
    (productChartCoordinate c) (productChartCoordinate b) 2).toRingHom)
  have hi : (f ≫ smoothProductSwap W) ≫ (smoothCurveProductOpen W).ι =
      (g ≫ s) ≫ projectiveAdditionInclusion W
        (productChartCoordinate c) (productChartCoordinate b) 2 ≫
          integralCurveProductChart W c b := by
    rw [Category.assoc, smoothProductSwap_inclusion, ← Category.assoc, h]
    simp only [Category.assoc]
    rw [integralCurveProductChart_swap]
    simpa only [s, Category.assoc] using congrArg
      (fun t => g ≫ t ≫ integralCurveProductChart W c b)
      (additionOutputSwap_inclusion W (productChartCoordinate c) (productChartCoordinate b) 2).symm
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := smoothCurveAddition_originalPolynomial W c b (f ≫ smoothProductSwap W) (g ≫ s) hi
  simp only [Category.assoc] at he ⊢
  rw [he, smoothCurveAddition_originalPolynomial W b c f g h]
  dsimp only [s]
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom (additionOutputSwap W
    (productChartCoordinate c) (productChartCoordinate b) 2).toRingHom)),
    projectiveAdditionSpec_swap]

/-- Smooth addition is symmetric whenever a mixed chart presents the inputs. -/
theorem smoothCurveAddition_swap_mixed (b c : Bool) (ha : b = false ∨ c = false)
    {X : Scheme.{u}} (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (h : f ≫ (smoothCurveProductOpen W).ι = g ≫ smoothProductChartInput W b c) :
    f ≫ smoothProductSwap W ≫ smoothCurveAddition W = f ≫ smoothCurveAddition W := by
  let C := smoothMixedCover W b c ha
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hh : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
      (q ≫ C.f i) ≫ smoothProductChartInput W b c := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  cases i
  · change (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
      (q ≫ smoothPolynomialToInputs W b c 2) ≫ smoothProductChartInput W b c at hh
    have hp : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ (polynomialSmoothInputOpen W
          (productChartCoordinate b) (productChartCoordinate c) 2).ι) ≫
            projectiveAdditionInclusion W
              (productChartCoordinate b) (productChartCoordinate c) 2 ≫
                integralCurveProductChart W b c := by
      simpa only [smoothProductChartInput, Category.assoc,
        smoothPolynomialToInputs_inclusion_assoc, smoothPolynomialInput] using hh
    simpa only [Category.assoc] using smoothCurveAddition_swap_polynomial W b c (p ≫ f) _ hp
  · change (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
      (q ≫ smoothAffineOverlapToChart W b c) ≫ smoothProductChartInput W b c at hh
    have hp : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothAffineOverlapToInputs W b c) ≫ (smoothAffineInputOpen W).ι ≫
          integralCurveProductChart W false false := by
      simpa only [Category.assoc, smoothAffineOverlapToInputs_global] using hh
    simpa only [Category.assoc] using smoothCurveAddition_swap_affine W (p ≫ f) _ hp

end FLT.Mazur.WeierstrassIntegralChart
