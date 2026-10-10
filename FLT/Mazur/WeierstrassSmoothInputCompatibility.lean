/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCrossPolynomial

/-!
# Compatibility of smooth addition across all input charts

The smooth affine and polynomial opens cover each mixed input product.
Their cross-chart comparisons identify the four complete smooth laws on
every common scheme, including schemes with nilpotents.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A mixed input chart's two smooth domains detect compatibility with any other chart. -/
theorem smoothInputAddition_mixed_commonScheme (b c d e : Bool)
    (ha : d = false ∨ e = false) {X : Scheme.{u}}
    (f : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (g : X ⟶ (smoothProductChartOpen W d e).toScheme)
    (h : f ≫ smoothProductChartInput W b c = g ≫ smoothProductChartInput W d e) :
    f ≫ smoothInputAddition W b c = g ≫ smoothInputAddition W d e := by
  let C := smoothMixedCover W d e ha
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hg : (p ≫ f) ≫ smoothProductChartInput W b c =
      (q ≫ C.f i) ≫ smoothProductChartInput W d e := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ smoothInputAddition W b c) =
    p ≫ (g ≫ smoothInputAddition W d e)
  rw [← Category.assoc p g, hi, Category.assoc]
  cases i
  · change p ≫ (f ≫ smoothInputAddition W b c) =
      q ≫ smoothPolynomialToInputs W d e 2 ≫ smoothInputAddition W d e
    rw [smoothInputAddition_polynomial]
    apply (cancel_mono (integralSmoothOpen W).ι).mp
    simp only [Category.assoc, polynomialSmoothChart_inclusion]
    have hh : (p ≫ f) ≫ smoothProductChartInput W b c =
        (q ≫ (polynomialSmoothInputOpen W
          (productChartCoordinate d) (productChartCoordinate e) 2).ι) ≫
            projectiveAdditionInclusion W
              (productChartCoordinate d) (productChartCoordinate e) 2 ≫
                integralCurveProductChart W d e := by
      change (p ≫ f) ≫ smoothProductChartInput W b c =
        (q ≫ smoothPolynomialToInputs W d e 2) ≫ smoothProductChartInput W d e at hg
      simpa only [smoothProductChartInput, Category.assoc,
        smoothPolynomialToInputs_inclusion_assoc, smoothPolynomialInput] using hg
    simpa only [Category.assoc] using
      smoothInputAddition_commonPolynomial W b c d e (p ≫ f) _ hh
  · change p ≫ (f ≫ smoothInputAddition W b c) =
      q ≫ smoothAffineOverlapToChart W d e ≫ smoothInputAddition W d e
    rw [smoothInputAddition_affine]
    have hh : (p ≫ f) ≫ smoothProductChartInput W b c =
        (q ≫ smoothAffineOverlapToInputs W d e) ≫ (smoothAffineInputOpen W).ι ≫
          integralCurveProductChart W false false := by
      change (p ≫ f) ≫ smoothProductChartInput W b c =
        (q ≫ smoothAffineOverlapToChart W d e) ≫ smoothProductChartInput W d e at hg
      simp only [Category.assoc] at hg
      rw [← smoothAffineOverlapToInputs_global] at hg
      simpa only [Category.assoc] using hg
    simpa only [Category.assoc, smoothAffineOverlapAddition] using
      smoothInputAddition_commonAffine W b c (p ≫ f) _ hh

/-- All four smooth chart laws agree whenever their original global input pairs agree. -/
theorem smoothInputAddition_commonScheme (b c d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (g : X ⟶ (smoothProductChartOpen W d e).toScheme)
    (h : f ≫ smoothProductChartInput W b c = g ≫ smoothProductChartInput W d e) :
    f ≫ smoothInputAddition W b c = g ≫ smoothInputAddition W d e := by
  cases d <;> cases e
  · exact smoothInputAddition_mixed_commonScheme W b c false false (.inl rfl) f g h
  · exact smoothInputAddition_mixed_commonScheme W b c false true (.inl rfl) f g h
  · exact smoothInputAddition_mixed_commonScheme W b c true false (.inr rfl) f g h
  · cases b <;> cases c
    · exact (smoothInputAddition_mixed_commonScheme W true true false false
        (.inl rfl) g f h.symm).symm
    · exact (smoothInputAddition_mixed_commonScheme W true true false true
        (.inl rfl) g f h.symm).symm
    · exact (smoothInputAddition_mixed_commonScheme W true true true false
        (.inr rfl) g f h.symm).symm
    · exact congrArg (fun a => a ≫ smoothInputAddition W true true)
        ((cancel_mono (smoothProductChartInput W true true)).mp h)

end FLT.Mazur.WeierstrassIntegralChart
