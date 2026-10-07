/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInputAdditionRestrictions
public import FLT.Mazur.WeierstrassIntegralProductOverlap
public import FLT.Mazur.WeierstrassPolynomialInputCurveComparison

/-!
# Comparing addition across input charts on affine and polynomial domains

The actual product-overlap universal property converts equality of global
inputs into the existing affine normalization and polynomial comparisons.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- On any scheme where both inputs are affine, every chart gives the affine addition law. -/
theorem integralInputAdditionToCurve_commonAffine (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (a : X ⟶ Spec (.of (AffineProduct W)))
    (h : f ≫ integralCurveProductChart W b c = a ≫ integralCurveProductChart W false false) :
    f ≫ integralInputAdditionToCurve W hΔ b c = a ≫ affineAdditionToCurve W hΔ := by
  obtain ⟨v, hv, ha⟩ := integralProductOverlap_exists_lift W b c false false f a h
  rw [← hv, Category.assoc]
  change v ≫ Spec.map (CommRingCat.ofHom (productOverlapRestriction W
    (productChartCoordinate b) (productChartCoordinate c) 2 2).toRingHom) ≫
      integralInputAdditionToCurve W hΔ b c = _
  rw [integralInputAdditionToCurve_affine, ← Category.assoc]
  change v ≫ affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) = a at ha
  exact congrArg (fun t => t ≫ affineAdditionToCurve W hΔ) ha

/-- Any common input scheme lying in a polynomial output-Z domain has the same addition. -/
theorem integralInputAdditionToCurve_commonPolynomial (b c d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate d) (productChartCoordinate e) 2)))
    (h : f ≫ integralCurveProductChart W b c =
      g ≫ projectiveAdditionInclusion W (productChartCoordinate d) (productChartCoordinate e) 2 ≫
        integralCurveProductChart W d e) :
    f ≫ integralInputAdditionToCurve W hΔ b c =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate d) (productChartCoordinate e) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  let j := productChartCoordinate d
  let k := productChartCoordinate e
  let j' := productChartCoordinate b
  let k' := productChartCoordinate c
  obtain ⟨v, hv, hv'⟩ := integralProductOverlap_exists_lift W d e b c
    (g ≫ projectiveAdditionInclusion W j k 2) f (by simpa only [Category.assoc] using h.symm)
  let l := (inputPolynomial_isPullback W j k j' k' 2).lift v g hv
  have hl : (l ≫ Spec.map (CommRingCat.ofHom
      (inputPolynomialOther W j k j' k' 2).toRingHom)) ≫
        projectiveAdditionInclusion W j' k' 2 = f := by
    rw [Category.assoc, inputPolynomialOther_inclusion, ← Category.assoc,
      IsPullback.lift_fst]
    exact hv'
  rw [← hl, Category.assoc, Category.assoc, integralInputAdditionToCurve_polynomial]
  have he := congrArg (fun t => l ≫ t ≫ integralCurveChart W 2)
    (inputPolynomialAddition_spec W j k j' k' 2)
  simpa only [Category.assoc, l, IsPullback.lift_snd_assoc] using he

end FLT.Mazur.WeierstrassIntegralChart
