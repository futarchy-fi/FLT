/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityIdentityCover
public import FLT.Mazur.WeierstrassGlobalAdditionZeroRestrictions

/-!
# The zero section is a two-sided identity for global addition

The affine chart and the concrete infinity identity neighborhoods cover the
whole cubic. Their scheme-level identities descend to the actual global
addition, without assuming density, reducedness or any group-law axioms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The left identity holds on the whole constructed infinity neighborhood. -/
theorem integralCurveAddition_leftZero_neighborhood :
    infinityIdentityInclusion W true ≫ integralCurveChart W 1 ≫
        integralCurveLeftZero W ≫ integralCurveAddition W hΔ =
      infinityIdentityInclusion W true ≫ integralCurveChart W 1 := by
  have hs := integralCurveChart_leftZero W true
  change integralCurveChart W 1 ≫ integralCurveLeftZero W = _ at hs
  rw [← Category.assoc (integralCurveChart W 1), hs,
    Category.assoc, integralCurveProductChart_addition]
  change infinityIdentityInclusion W true ≫
    Spec.map (CommRingCat.ofHom (infinityIdentityInput W true).toRingHom) ≫
      yProductAdditionToCurve W hΔ = _
  rw [← Category.assoc, ← infinityIdentitySpec_inputs, Category.assoc,
    yProductAdditionToCurve_infinity, ← Category.assoc, infinityIdentitySpec_addition]

/-- The right identity holds on the opposite infinity neighborhood. -/
theorem integralCurveAddition_rightZero_neighborhood :
    infinityIdentityInclusion W false ≫ integralCurveChart W 1 ≫
        integralCurveRightZero W ≫ integralCurveAddition W hΔ =
      infinityIdentityInclusion W false ≫ integralCurveChart W 1 := by
  have hs := integralCurveChart_rightZero W true
  change integralCurveChart W 1 ≫ integralCurveRightZero W = _ at hs
  rw [← Category.assoc (integralCurveChart W 1), hs,
    Category.assoc, integralCurveProductChart_addition]
  change infinityIdentityInclusion W false ≫
    Spec.map (CommRingCat.ofHom (infinityIdentityInput W false).toRingHom) ≫
      yProductAdditionToCurve W hΔ = _
  rw [← Category.assoc, ← infinityIdentitySpec_inputs, Category.assoc,
    yProductAdditionToCurve_infinity, ← Category.assoc, infinityIdentitySpec_addition]

/-- The affine overlap and identity neighborhood give the left identity on all of Y. -/
theorem integralCurveAddition_leftZero_yChart :
    integralCurveChart W 1 ≫ integralCurveLeftZero W ≫ integralCurveAddition W hΔ =
      integralCurveChart W 1 := by
  apply (infinityIdentityCover W true).hom_ext
  intro c
  cases c
  · change overlapInclusion W 1 2 ≫ _ = overlapInclusion W 1 2 ≫ _
    rw [← Category.assoc, ← integralCurve_output_transition, Category.assoc,
      integralCurveAddition_leftZero_affine, integralCurve_output_transition]
  · exact integralCurveAddition_leftZero_neighborhood W hΔ

/-- The same two-open argument gives the right identity on all of Y. -/
theorem integralCurveAddition_rightZero_yChart :
    integralCurveChart W 1 ≫ integralCurveRightZero W ≫ integralCurveAddition W hΔ =
      integralCurveChart W 1 := by
  apply (infinityIdentityCover W false).hom_ext
  intro c
  cases c
  · change overlapInclusion W 1 2 ≫ _ = overlapInclusion W 1 2 ≫ _
    rw [← Category.assoc, ← integralCurve_output_transition, Category.assoc,
      integralCurveAddition_rightZero_affine, integralCurve_output_transition]
  · exact integralCurveAddition_rightZero_neighborhood W hΔ

/-- Zero is a left identity for the constructed global regular addition. -/
theorem integralCurveAddition_left_identity :
    integralCurveLeftZero W ≫ integralCurveAddition W hΔ = 𝟙 (integralCurve W) := by
  apply (integralCurveTwoChartCover W).hom_ext
  intro b
  cases b
  · change integralCurveChart W 2 ≫ _ = integralCurveChart W 2 ≫ 𝟙 _
    rw [integralCurveAddition_leftZero_affine, Category.comp_id]
  · change integralCurveChart W 1 ≫ _ = integralCurveChart W 1 ≫ 𝟙 _
    rw [integralCurveAddition_leftZero_yChart, Category.comp_id]

/-- Zero is a right identity for the constructed global regular addition. -/
theorem integralCurveAddition_right_identity :
    integralCurveRightZero W ≫ integralCurveAddition W hΔ = 𝟙 (integralCurve W) := by
  apply (integralCurveTwoChartCover W).hom_ext
  intro b
  cases b
  · change integralCurveChart W 2 ≫ _ = integralCurveChart W 2 ≫ 𝟙 _
    rw [integralCurveAddition_rightZero_affine, Category.comp_id]
  · change integralCurveChart W 1 ≫ _ = integralCurveChart W 1 ≫ 𝟙 _
    rw [integralCurveAddition_rightZero_yChart, Category.comp_id]

end FLT.Mazur.WeierstrassIntegralChart
