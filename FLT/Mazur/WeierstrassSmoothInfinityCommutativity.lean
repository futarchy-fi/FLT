/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothMixedCommutativity
public import FLT.Mazur.WeierstrassSwappedInfinitySchemes

/-!
# Smooth commutativity on the infinity domain

Pulling the smooth Y-product cover back along reversed inputs reduces symmetry
to the affine, polynomial, and actual reversed infinity comparisons.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Involutive input interchange allows symmetry to be checked after a swap. -/
theorem smoothCurveAddition_swap_of_swapped {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (h : (f ≫ smoothProductSwap W) ≫ smoothProductSwap W ≫ smoothCurveAddition W =
      (f ≫ smoothProductSwap W) ≫ smoothCurveAddition W) :
    f ≫ smoothProductSwap W ≫ smoothCurveAddition W = f ≫ smoothCurveAddition W := by
  simpa only [Category.assoc, smoothProductSwap_swap_assoc, Category.id_comp] using h.symm

/-- The full smooth addition is symmetric on every original infinity presentation. -/
theorem smoothCurveAddition_swap_infinity {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ (smoothCurveProductOpen W).ι =
      g ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true) :
    f ≫ smoothProductSwap W ≫ smoothCurveAddition W = f ≫ smoothCurveAddition W := by
  let v := f ≫ smoothProductSwap W
  let a := g ≫ infinityAdditionInclusion W ≫ infinityInputSwap W
  have hs : infinityInputSwap W ≫ integralCurveProductChart W true true =
      integralCurveProductChart W true true ≫ integralCurveSwap W :=
    (integralCurveProductChart_swap W true true).symm
  have ha : a ≫ integralCurveProductChart W true true =
      v ≫ (smoothCurveProductOpen W).ι := by
    simp only [a, v, Category.assoc, smoothProductSwap_inclusion]
    rw [hs, ← Category.assoc f, h]
    simp only [Category.assoc]
  let l := smoothProductChartLift W true true v a ha
  have hl : l ≫ smoothProductChartInput W true true =
      v ≫ (smoothCurveProductOpen W).ι := by
    rw [smoothProductChartInput, ← Category.assoc]
    exact (congrArg (fun q => q ≫ integralCurveProductChart W true true)
      (IsOpenImmersion.lift_fac _ _ _)).trans ha
  let C := smoothYCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ l)
  intro i
  let p := (C.pullback₁ l).f i
  let q := Scheme.Cover.pullbackHom C l i
  have hi : p ≫ l = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C l i).symm
  have hh : (p ≫ v) ≫ (smoothCurveProductOpen W).ι =
      (q ≫ C.f i) ≫ smoothProductChartInput W true true := by
    rw [Category.assoc, ← hl, ← Category.assoc, hi]
  cases i
  · suffices he : (p ≫ v) ≫ smoothProductSwap W ≫ smoothCurveAddition W =
        (p ≫ v) ≫ smoothCurveAddition W by
      simpa only [Category.assoc] using smoothCurveAddition_swap_of_swapped W (p ≫ f)
        (by simpa only [v, Category.assoc] using he)
    have hp : (p ≫ v) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothAffineOverlapToInputs W true true) ≫ (smoothAffineInputOpen W).ι ≫
          integralCurveProductChart W false false := by
      change (p ≫ v) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothAffineOverlapToChart W true true) ≫
          smoothProductChartInput W true true at hh
      simpa only [Category.assoc, smoothAffineOverlapToInputs_global] using hh
    simpa only [v, Category.assoc] using smoothCurveAddition_swap_affine W (p ≫ v) _ hp
  · suffices he : (p ≫ v) ≫ smoothProductSwap W ≫ smoothCurveAddition W =
        (p ≫ v) ≫ smoothCurveAddition W by
      simpa only [Category.assoc] using smoothCurveAddition_swap_of_swapped W (p ≫ f)
        (by simpa only [v, Category.assoc] using he)
    have hp : (p ≫ v) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ (polynomialSmoothInputOpen W 1 1 2).ι) ≫
          projectiveAdditionInclusion W 1 1 2 ≫ integralCurveProductChart W true true := by
      change (p ≫ v) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothPolynomialToInputs W true true 2) ≫
          smoothProductChartInput W true true at hh
      simp only [smoothProductChartInput, Category.assoc,
        smoothPolynomialToInputs_inclusion_assoc, smoothPolynomialInput] at hh
      exact hh
    simpa only [v, Category.assoc] using
      smoothCurveAddition_swap_polynomial W true true (p ≫ v) _ hp
  · have hp : (p ≫ v) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ (infinitySmoothInputOpen W).ι) ≫
          infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
      change (p ≫ v) ≫ (smoothCurveProductOpen W).ι =
        (q ≫ smoothInfinityToInputs W) ≫ smoothProductChartInput W true true at hh
      simpa only [smoothProductChartInput, Category.assoc,
        smoothInfinityToInputs_inclusion_assoc, smoothInfinityInput] using hh
    have ho : (p ≫ f) ≫ (smoothCurveProductOpen W).ι =
        (p ≫ g) ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
      rw [Category.assoc, h, Category.assoc]
    have hab : (q ≫ (infinitySmoothInputOpen W).ι) ≫ infinityAdditionInclusion W =
        (p ≫ g) ≫ infinityAdditionInclusion W ≫ infinityInputSwap W := by
      apply (cancel_mono (integralCurveProductChart W true true)).mp
      calc
        ((q ≫ (infinitySmoothInputOpen W).ι) ≫ infinityAdditionInclusion W) ≫
            integralCurveProductChart W true true =
            (p ≫ v) ≫ (smoothCurveProductOpen W).ι := by
          simpa only [Category.assoc] using hp.symm
        _ = ((p ≫ g) ≫ infinityAdditionInclusion W ≫ infinityInputSwap W) ≫
            integralCurveProductChart W true true := by
          rw [Category.assoc, ← ha]
          simp only [a, Category.assoc]
    apply (cancel_mono (integralSmoothOpen W).ι).mp
    have he := smoothCurveAddition_originalInfinity W (p ≫ v) _ hp
    have he' := smoothCurveAddition_originalInfinity W (p ≫ f) _ ho
    have hout := congrArg (fun t => t ≫ integralCurveChart W 1)
      (infinityAddition_swap_commonScheme W _ _ hab)
    simpa only [v, Category.assoc] using he.trans (hout.trans he'.symm)

end FLT.Mazur.WeierstrassIntegralChart
