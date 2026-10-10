/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInverseCover
public import FLT.Mazur.WeierstrassInfinityInverseScheme

/-!
# Two-sided inverse laws for the global regular addition

The affine inverse identity and the explicit infinity neighborhood cover the
whole cubic. Their scheme-level identities descend to the right inverse law.
Precomposing with the involutive negation yields the left inverse law.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The right inverse identity holds on the entire Y chart. -/
theorem integralCurveAddition_rightNegation_yChart :
    integralCurveChart W 1 ≫ integralCurveRightNegation W ≫ integralCurveAddition W hΔ =
      integralCurveChart W 1 ≫ integralCurveStructure W ≫ integralCurveZero W := by
  apply (infinityInverseCover W).hom_ext
  intro b
  cases b
  · change overlapInclusion W 1 2 ≫ _ = overlapInclusion W 1 2 ≫ _
    have h := congrArg
      (fun t => Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) ≫ t)
      (integralCurveAddition_rightNegation_affine W hΔ)
    simpa only [← Category.assoc, integralCurve_output_transition] using h
  · exact integralCurveAddition_rightNegation_neighborhood W hΔ

/-- Pairing any point with its constructed negation adds to the base-valued zero section. -/
theorem integralCurveAddition_right_inverse :
    integralCurveRightNegation W ≫ integralCurveAddition W hΔ =
      integralCurveStructure W ≫ integralCurveZero W := by
  apply (integralCurveTwoChartCover W).hom_ext
  intro b
  cases b
  · exact integralCurveAddition_rightNegation_affine W hΔ
  · exact integralCurveAddition_rightNegation_yChart W hΔ

/-- Negation is also a left inverse for the constructed global regular addition. -/
theorem integralCurveAddition_left_inverse :
    integralCurveLeftNegation W ≫ integralCurveAddition W hΔ =
      integralCurveStructure W ≫ integralCurveZero W := by
  rw [← integralCurveNegation_rightNegation, Category.assoc,
    integralCurveAddition_right_inverse, ← Category.assoc, integralCurveNegation_structure]

end FLT.Mazur.WeierstrassIntegralChart
