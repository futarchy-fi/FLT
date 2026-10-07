/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# Global addition on the affine identity sections and the zero pair

Transport the existing polynomial identity formulas and infinity-pair formula
through the global restriction theorems. These are identities of scheme maps,
including over nonreduced coefficient rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The left affine infinity evaluation lifts to the polynomial addition domain. -/
theorem leftInfinityLift_inclusion :
    Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom) ≫
        projectiveAdditionInclusion W 1 2 2 =
      Spec.map (CommRingCat.ofHom (chartProductAtLeftInfinity W 2).toRingHom) := by
  rw [projectiveAdditionInclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact chartProductLeftInfinityLift_restriction W

/-- The right affine infinity evaluation also lifts to the polynomial domain. -/
theorem rightInfinityLift_inclusion :
    Spec.map (CommRingCat.ofHom (chartProductRightInfinityLift W).toRingHom) ≫
        projectiveAdditionInclusion W 2 1 2 =
      Spec.map (CommRingCat.ofHom (chartProductAtRightInfinity W 2).toRingHom) := by
  rw [projectiveAdditionInclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact chartProductRightInfinityLift_restriction W

/-- Global addition by zero on the left fixes the whole affine curve chart. -/
theorem integralCurveAddition_leftZero_affine :
    integralCurveChart W 2 ≫ integralCurveLeftZero W ≫ integralCurveAddition W hΔ =
      integralCurveChart W 2 := by
  change integralCurveChart W (productChartCoordinate false) ≫
    integralCurveLeftZero W ≫ integralCurveAddition W hΔ = _
  erw [← Category.assoc, integralCurveChart_leftZero W false,
    Category.assoc, integralCurveProductChart_addition, ← leftInfinityLift_inclusion,
    Category.assoc]
  change Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom) ≫
    projectiveAdditionInclusion W 1 2 2 ≫ integralInputAdditionToCurve W hΔ true false = _
  erw [integralInputAdditionToCurve_polynomial W hΔ true false]
  change Spec.map (CommRingCat.ofHom (chartProductLeftInfinityLift W).toRingHom) ≫
    projectiveAdditionChartSpec W 1 2 2 ≫ integralCurveChart W 2 = _
  rw [← Category.assoc, projectiveAdditionChartSpec_left_identity, Category.id_comp]

/-- Global addition by zero on the right fixes the whole affine curve chart. -/
theorem integralCurveAddition_rightZero_affine :
    integralCurveChart W 2 ≫ integralCurveRightZero W ≫ integralCurveAddition W hΔ =
      integralCurveChart W 2 := by
  change integralCurveChart W (productChartCoordinate false) ≫
    integralCurveRightZero W ≫ integralCurveAddition W hΔ = _
  erw [← Category.assoc, integralCurveChart_rightZero W false,
    Category.assoc, integralCurveProductChart_addition, ← rightInfinityLift_inclusion,
    Category.assoc]
  change Spec.map (CommRingCat.ofHom (chartProductRightInfinityLift W).toRingHom) ≫
    projectiveAdditionInclusion W 2 1 2 ≫ integralInputAdditionToCurve W hΔ false true = _
  erw [integralInputAdditionToCurve_polynomial W hΔ false true]
  change Spec.map (CommRingCat.ofHom (chartProductRightInfinityLift W).toRingHom) ≫
    projectiveAdditionChartSpec W 2 1 2 ≫ integralCurveChart W 2 = _
  rw [← Category.assoc, projectiveAdditionChartSpec_right_identity, Category.id_comp]

/-- The original infinity pair is precisely the pair of global zero sections. -/
theorem infinityPairEvaluation_global :
    Spec.map (CommRingCat.ofHom (infinityPairEvaluation W).toRingHom) ≫
        integralCurveProductChart W true true =
      pullback.lift (integralCurveZero W) (integralCurveZero W) rfl := by
  apply pullback.hom_ext
  · rw [Category.assoc, integralCurveProductChart_fst, pullback.lift_fst,
      ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((infinityPairEvaluation W).comp (chartProductLeft W 1 1)).toRingHom) ≫ _ = _
    rw [infinityPairEvaluation, chartProductEvaluation_left]
    rfl
  · rw [Category.assoc, integralCurveProductChart_snd, pullback.lift_snd,
      ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((infinityPairEvaluation W).comp (chartProductRight W 1 1)).toRingHom) ≫ _ = _
    rw [infinityPairEvaluation, chartProductEvaluation_right]
    rfl

/-- The sum of the two zero sections is the zero section over the whole base. -/
theorem integralCurveAddition_zero_zero :
    pullback.lift (integralCurveZero W) (integralCurveZero W) rfl ≫
      integralCurveAddition W hΔ = integralCurveZero W := by
  rw [← infinityPairEvaluation_global, Category.assoc, integralCurveProductChart_addition,
    ← infinityPairSectionSpec_inclusion, Category.assoc]
  change infinityPairSectionSpec W ≫ infinityAdditionInclusion W ≫
    yProductAdditionToCurve W hΔ = _
  rw [yProductAdditionToCurve_infinity, ← Category.assoc, infinityPairSectionSpec_addition]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
