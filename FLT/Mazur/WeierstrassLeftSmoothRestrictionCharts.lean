/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothOriginalFormulas
public import FLT.Mazur.WeierstrassSmoothAdditionGluing

/-!
# Restricting enlarged translation to the original smooth chart laws

Comparisons use the actual affine, polynomial and infinity domains of smooth
addition. Thus the enlarged law retains the original group law on every smooth
input chart, including arbitrary scheme-valued inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- On smooth affine inputs the enlarged global law is the original smooth law. -/
theorem leftSmoothCurveAddition_smoothAffine {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothAffineInputOpen W).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι =
      g ≫ (smoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false) :
    f ≫ leftSmoothCurveAddition W = g ≫ smoothAffineAddition W ≫ (integralSmoothOpen W).ι := by
  have hi : f ≫ (leftSmoothCurveProductOpen W).ι =
      (g ≫ smoothAffineToLeftSmooth W) ≫ (leftSmoothAffineInputOpen W).ι ≫
        integralCurveProductChart W false false := by
    rw [Category.assoc, smoothAffineToLeftSmooth_inclusion_assoc]
    exact h
  rw [leftSmoothCurveAddition_originalAffine W f _ hi,
    Category.assoc, smoothAffineToLeftSmooth_addition]

/-- On any transported smooth affine domain the original law is retained. -/
theorem leftSmoothCurveAddition_smoothOverlap (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothAffineOverlapOpen W b c).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι =
      g ≫ smoothAffineOverlapToChart W b c ≫ smoothProductChartInput W b c) :
    f ≫ leftSmoothCurveAddition W =
      g ≫ smoothAffineOverlapAddition W b c ≫ (integralSmoothOpen W).ι := by
  have hi : f ≫ (leftSmoothCurveProductOpen W).ι =
      (g ≫ smoothAffineOverlapToInputs W b c) ≫ (smoothAffineInputOpen W).ι ≫
        integralCurveProductChart W false false := by
    rw [Category.assoc, smoothAffineOverlapToInputs_global]
    exact h
  simpa only [smoothAffineOverlapAddition, Category.assoc] using
    leftSmoothCurveAddition_smoothAffine W f _ hi

/-- A complete mixed smooth chart retains its original law under enlarged translation. -/
theorem leftSmoothCurveAddition_smoothMixed (b c : Bool) (ha : b = false ∨ c = false)
    {X : Scheme.{u}} (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι = g ≫ smoothProductChartInput W b c) :
    f ≫ leftSmoothCurveAddition W =
      g ≫ smoothMixedAddition W b c ha ≫ (integralSmoothOpen W).ι := by
  let C := smoothMixedCover W b c ha
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := C.pullbackHom g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hg : (p ≫ f) ≫ (leftSmoothCurveProductOpen W).ι =
      (q ≫ C.f i) ≫ smoothProductChartInput W b c := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ leftSmoothCurveAddition W) =
    p ≫ (g ≫ smoothMixedAddition W b c ha ≫ (integralSmoothOpen W).ι)
  rw [← Category.assoc p g, hi, Category.assoc]
  change _ = q ≫ smoothMixedInclusion W b c i ≫
    smoothMixedAddition W b c ha ≫ (integralSmoothOpen W).ι
  rw [smoothMixedLocal_glued_assoc]
  cases i
  · change _ = q ≫ polynomialSmoothChart W _ _ 2 ≫ (integralSmoothOpen W).ι
    rw [polynomialSmoothChart_inclusion]
    have hh : (p ≫ f) ≫ (leftSmoothCurveProductOpen W).ι =
        (q ≫ (polynomialSmoothInputOpen W
          (productChartCoordinate b) (productChartCoordinate c) 2).ι) ≫
            projectiveAdditionInclusion W
              (productChartCoordinate b) (productChartCoordinate c) 2 ≫
                integralCurveProductChart W b c := by
      change _ = (q ≫ smoothPolynomialToInputs W b c 2) ≫ smoothProductChartInput W b c at hg
      simpa only [smoothProductChartInput, Category.assoc,
        smoothPolynomialToInputs_inclusion_assoc, smoothPolynomialInput] using hg
    simpa only [Category.assoc] using
      leftSmoothCurveAddition_originalPolynomial W b c (p ≫ f) _ hh
  · change _ = q ≫ smoothAffineOverlapAddition W b c ≫ (integralSmoothOpen W).ι
    have hh : (p ≫ f) ≫ (leftSmoothCurveProductOpen W).ι =
        q ≫ smoothAffineOverlapToChart W b c ≫ smoothProductChartInput W b c := by
      change _ = (q ≫ smoothAffineOverlapToChart W b c) ≫ smoothProductChartInput W b c at hg
      simpa only [Category.assoc] using hg
    simpa only [Category.assoc] using leftSmoothCurveAddition_smoothOverlap W b c (p ≫ f) q hh

/-- The complete smooth Y/Y chart retains all three original local formulas. -/
theorem leftSmoothCurveAddition_smoothY {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothProductChartOpen W true true).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι = g ≫ smoothProductChartInput W true true) :
    f ≫ leftSmoothCurveAddition W = g ≫ smoothYAddition W ≫ (integralSmoothOpen W).ι := by
  let C := smoothYCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := C.pullbackHom g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hg : (p ≫ f) ≫ (leftSmoothCurveProductOpen W).ι =
      (q ≫ C.f i) ≫ smoothProductChartInput W true true := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ leftSmoothCurveAddition W) =
    p ≫ (g ≫ smoothYAddition W ≫ (integralSmoothOpen W).ι)
  rw [← Category.assoc p g, hi, Category.assoc]
  change _ = q ≫ smoothYInclusion W i ≫ smoothYAddition W ≫ (integralSmoothOpen W).ι
  rw [smoothYLocal_glued_assoc]
  cases i
  · change _ = q ≫ smoothAffineOverlapAddition W true true ≫ (integralSmoothOpen W).ι
    have hh : (p ≫ f) ≫ (leftSmoothCurveProductOpen W).ι =
        q ≫ smoothAffineOverlapToChart W true true ≫ smoothProductChartInput W true true := by
      change _ = (q ≫ smoothAffineOverlapToChart W true true) ≫
        smoothProductChartInput W true true at hg
      simpa only [Category.assoc] using hg
    simpa only [Category.assoc] using
      leftSmoothCurveAddition_smoothOverlap W true true (p ≫ f) q hh
  · change _ = q ≫ polynomialSmoothChart W
      (productChartCoordinate true) (productChartCoordinate true) 2 ≫ (integralSmoothOpen W).ι
    rw [polynomialSmoothChart_inclusion]
    have hh : (p ≫ f) ≫ (leftSmoothCurveProductOpen W).ι =
        (q ≫ (polynomialSmoothInputOpen W
          (productChartCoordinate true) (productChartCoordinate true) 2).ι) ≫
            projectiveAdditionInclusion W
              (productChartCoordinate true) (productChartCoordinate true) 2 ≫
                integralCurveProductChart W true true := by
      change _ = (q ≫ smoothPolynomialToInputs W true true 2) ≫
        smoothProductChartInput W true true at hg
      simpa only [smoothProductChartInput, Category.assoc,
        smoothPolynomialToInputs_inclusion_assoc, smoothPolynomialInput] using hg
    simpa only [Category.assoc] using
      leftSmoothCurveAddition_originalPolynomial W true true (p ≫ f) _ hh
  · change _ = q ≫ infinitySmoothChart W ≫ (integralSmoothOpen W).ι
    rw [infinitySmoothChart_inclusion]
    have hh : (p ≫ f) ≫ (leftSmoothCurveProductOpen W).ι =
        (q ≫ (infinitySmoothInputOpen W).ι) ≫
          infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
      change _ = (q ≫ smoothInfinityToInputs W) ≫ smoothProductChartInput W true true at hg
      simpa only [smoothProductChartInput, Category.assoc,
        smoothInfinityToInputs_inclusion_assoc, smoothInfinityInput] using hg
    simpa only [Category.assoc, infinityAdditionSpec] using
      leftSmoothCurveAddition_originalInfinity W (p ≫ f) _ hh

/-- All four smooth input charts compute the original smooth group law. -/
theorem leftSmoothCurveAddition_smoothChart (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι = g ≫ smoothProductChartInput W b c) :
    f ≫ leftSmoothCurveAddition W =
      g ≫ smoothInputAddition W b c ≫ (integralSmoothOpen W).ι := by
  cases b <;> cases c
  · exact leftSmoothCurveAddition_smoothMixed W false false (.inl rfl) f g h
  · exact leftSmoothCurveAddition_smoothMixed W false true (.inl rfl) f g h
  · exact leftSmoothCurveAddition_smoothMixed W true false (.inr rfl) f g h
  · exact leftSmoothCurveAddition_smoothY W f g h

end FLT.Mazur.WeierstrassIntegralChart
