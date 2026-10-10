/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothYProductCover
public import FLT.Mazur.WeierstrassSmoothMixedAddition

/-!
# Compatibility of all three smooth Y/Y addition laws

The affine, polynomial, and infinity restrictions agree as morphisms on
arbitrary common schemes, without assumptions on reduction or nilpotents.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The smooth affine and infinity laws agree on their full common input domain. -/
theorem smoothAffineOverlap_infinity_smooth {X : Scheme.{u}}
    (f : X ⟶ (smoothAffineOverlapOpen W true true).toScheme)
    (g : X ⟶ (infinitySmoothInputOpen W).toScheme)
    (h : f ≫ smoothAffineOverlapInput W true true = g ≫ smoothInfinityInput W) :
    f ≫ smoothAffineOverlapAddition W true true = g ≫ infinitySmoothChart W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, infinitySmoothChart_inclusion]
  have he := smoothAffineOverlap_infinity W f (g ≫ (infinitySmoothInputOpen W).ι)
    (by simpa only [smoothInfinityInput, Category.assoc] using h)
  simpa only [Category.assoc, infinityAdditionSpec] using he

/-- The smooth infinity and polynomial laws agree on every common scheme. -/
theorem smoothInfinity_polynomial {X : Scheme.{u}} (t : Fin 3)
    (f : X ⟶ (infinitySmoothInputOpen W).toScheme)
    (g : X ⟶ (polynomialSmoothInputOpen W 1 1 t).toScheme)
    (h : f ≫ smoothInfinityInput W = g ≫ smoothPolynomialInput W true true t) :
    f ≫ infinitySmoothChart W = g ≫ polynomialSmoothChart W 1 1 t := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, infinitySmoothChart_inclusion, polynomialSmoothChart_inclusion]
  have he := infinityPolynomial_curve_eq W t
    (f ≫ (infinitySmoothInputOpen W).ι) (g ≫ (polynomialSmoothInputOpen W 1 1 t).ι)
    (by
      change f ≫ ((infinitySmoothInputOpen W).ι ≫ infinityAdditionInclusion W) =
        g ≫ ((polynomialSmoothInputOpen W 1 1 t).ι ≫
          projectiveAdditionInclusion W 1 1 t) at h
      simpa only [Category.assoc] using h)
  simpa only [Category.assoc, infinityAdditionSpec] using he

/-- The three original formulas take values in the relative smooth curve. -/
def smoothYLocal (i : YProductCoverIndex) :
    smoothYDomain W i ⟶ (integralSmoothOpen W).toScheme :=
  match i with
  | .affine => smoothAffineOverlapAddition W true true
  | .polynomial => polynomialSmoothChart W 1 1 2
  | .infinity => infinitySmoothChart W

/-- The restricted local laws agree for every presentation of the same Y/Y input. -/
theorem smoothYLocal_commonScheme (i j : YProductCoverIndex) {X : Scheme.{u}}
    (f : X ⟶ smoothYDomain W i) (g : X ⟶ smoothYDomain W j)
    (h : f ≫ smoothYInclusion W i = g ≫ smoothYInclusion W j) :
    f ≫ smoothYLocal W i = g ≫ smoothYLocal W j := by
  have hi := congrArg (fun a => a ≫ (smoothProductChartOpen W true true).ι) h
  cases i <;> cases j
  · exact congrArg (fun a => a ≫ smoothYLocal W .affine)
      ((cancel_mono (smoothYInclusion W .affine)).mp h)
  · apply smoothAffineOverlap_polynomial_smooth W true true 2 f g
    simpa only [Category.assoc, smoothYInclusion,
      smoothAffineOverlapToChart_inclusion, smoothPolynomialToInputs_inclusion] using hi
  · apply smoothAffineOverlap_infinity_smooth W f g
    simpa only [Category.assoc, smoothYInclusion,
      smoothAffineOverlapToChart_inclusion, smoothInfinityToInputs_inclusion] using hi
  · symm
    apply smoothAffineOverlap_polynomial_smooth W true true 2 g f
    simpa only [Category.assoc, smoothYInclusion,
      smoothAffineOverlapToChart_inclusion, smoothPolynomialToInputs_inclusion] using hi.symm
  · exact congrArg (fun a => a ≫ smoothYLocal W .polynomial)
      ((cancel_mono (smoothYInclusion W .polynomial)).mp h)
  · symm
    apply smoothInfinity_polynomial W 2 g f
    simpa only [Category.assoc, smoothYInclusion,
      smoothPolynomialToInputs_inclusion, smoothInfinityToInputs_inclusion] using hi.symm
  · symm
    apply smoothAffineOverlap_infinity_smooth W g f
    simpa only [Category.assoc, smoothYInclusion,
      smoothAffineOverlapToChart_inclusion, smoothInfinityToInputs_inclusion] using hi.symm
  · apply smoothInfinity_polynomial W 2 f g
    simpa only [Category.assoc, smoothYInclusion,
      smoothPolynomialToInputs_inclusion, smoothInfinityToInputs_inclusion] using hi
  · exact congrArg (fun a => a ≫ smoothYLocal W .infinity)
      ((cancel_mono (smoothYInclusion W .infinity)).mp h)

end FLT.Mazur.WeierstrassIntegralChart
