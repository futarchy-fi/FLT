/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothInfinityCommutativity

/-!
# Commutativity of addition on the full smooth curve

The complete smooth Y/Y cover and the mixed input covers prove symmetry on
all smooth pairs, including every bad reduction fiber.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- All three smooth Y/Y domains retain commutativity. -/
theorem smoothCurveAddition_swap_yChart {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothProductChartOpen W true true).toScheme)
    (h : f ≫ (smoothCurveProductOpen W).ι = g ≫ smoothProductChartInput W true true) :
    f ≫ smoothProductSwap W ≫ smoothCurveAddition W = f ≫ smoothCurveAddition W := by
  let C := smoothYCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hh : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
      (q ≫ C.f i) ≫ smoothProductChartInput W true true := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  cases i
  · have hp : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothAffineOverlapToInputs W true true) ≫ (smoothAffineInputOpen W).ι ≫
          integralCurveProductChart W false false := by
      change (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothAffineOverlapToChart W true true) ≫
          smoothProductChartInput W true true at hh
      simpa only [Category.assoc, smoothAffineOverlapToInputs_global] using hh
    simpa only [Category.assoc] using smoothCurveAddition_swap_affine W (p ≫ f) _ hp
  · have hp : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ (polynomialSmoothInputOpen W 1 1 2).ι) ≫
          projectiveAdditionInclusion W 1 1 2 ≫ integralCurveProductChart W true true := by
      change (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothPolynomialToInputs W true true 2) ≫
          smoothProductChartInput W true true at hh
      simp only [smoothProductChartInput, Category.assoc,
        smoothPolynomialToInputs_inclusion_assoc, smoothPolynomialInput] at hh
      exact hh
    simpa only [Category.assoc] using
      smoothCurveAddition_swap_polynomial W true true (p ≫ f) _ hp
  · have hp : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ (infinitySmoothInputOpen W).ι) ≫
          infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
      change (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothInfinityToInputs W) ≫ smoothProductChartInput W true true at hh
      simpa only [smoothProductChartInput, Category.assoc,
        smoothInfinityToInputs_inclusion_assoc, smoothInfinityInput] using hh
    simpa only [Category.assoc] using smoothCurveAddition_swap_infinity W (p ≫ f) _ hp

/-- The global law is commutative on the entire smooth input product. -/
@[reassoc] theorem smoothCurveAddition_commutative :
    smoothProductSwap W ≫ smoothCurveAddition W = smoothCurveAddition W := by
  apply (smoothCurveProductCover W).hom_ext
  rintro ⟨b, c⟩
  let f := (smoothCurveProductCover W).f (b, c)
  let g := smoothCurveProductCoverToChart W b c
  have h : f ≫ (smoothCurveProductOpen W).ι = g ≫ smoothProductChartInput W b c :=
    (smoothCurveProductCoverToChart_inputs W b c).symm
  cases b <;> cases c
  · exact smoothCurveAddition_swap_mixed W false false (.inl rfl) f g h
  · exact smoothCurveAddition_swap_mixed W false true (.inl rfl) f g h
  · exact smoothCurveAddition_swap_mixed W true false (.inr rfl) f g h
  · exact smoothCurveAddition_swap_yChart W f g h

/-- The actual categorical smooth addition is commutative. -/
@[reassoc] theorem smoothFactorAddition_commutative :
    smoothFactorSwap W ≫ smoothFactorAddition W = smoothFactorAddition W := by
  rw [smoothFactorAddition, smoothFactorSwap_toProduct_assoc, smoothCurveAddition_commutative]

end FLT.Mazur.WeierstrassIntegralChart
