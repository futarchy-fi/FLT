/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAdditionGluing

/-!
# Integral translation respects the original coefficient scheme

Each genuine local formula is over the coefficient ring. Descent through the
actual input covers makes the enlarged global law a morphism over that base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Transported enlarged affine addition preserves coefficients. -/
@[reassoc] theorem leftSmoothAffineOverlapAddition_structure (b c : Bool) :
    leftSmoothAffineOverlapAddition W b c ≫ integralCurveStructure W =
      leftSmoothAffineOverlapInput W b c ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))) := by
  rw [leftSmoothAffineOverlapAddition, Category.assoc, leftSmoothAffineAddition_structure,
    leftSmoothAffineOverlapToInputs_inclusion_assoc, leftSmoothAffineOverlapInput,
    Category.assoc]
  congr 1
  exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm

/-- Each unrestricted polynomial formula is over the original coefficient base. -/
theorem leftSmoothPolynomial_structure (j k t : Fin 3) :
    Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) ≫
        integralCurveChart W t ≫ integralCurveStructure W =
      projectiveAdditionInclusion W j k t ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W j k))) := by
  rw [integralCurveChart_structure]
  exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm

/-- The original regular infinity formula preserves the coefficient base. -/
theorem leftSmoothInfinity_structure :
    infinityAdditionSpec W ≫ integralCurveChart W 1 ≫ integralCurveStructure W =
      infinityAdditionInclusion W ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1))) := by
  rw [integralCurveChart_structure]
  exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm

/-- The complete mixed-chart law respects coefficients. -/
theorem leftSmoothMixedAddition_structure (b c : Bool) (ha : b = false ∨ c = false) :
    leftSmoothMixedAddition W b c ha ≫ integralCurveStructure W =
      (leftSmoothProductChartOpen W b c).ι ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))) := by
  apply (leftSmoothMixedCover W b c ha).hom_ext
  intro i
  rw [← Category.assoc, leftSmoothMixedLocal_glued]
  cases i
  · change (leftSmoothMixedProjection W b c ha false ≫ _ ≫ _) ≫ _ = _
    rw [Category.assoc, Category.assoc, leftSmoothPolynomial_structure]
    change leftSmoothMixedProjection W b c ha false ≫
      mixedProductCoverInclusion W (productChartCoordinate b) (productChartCoordinate c)
        false ≫ _ = _
    rw [leftSmoothMixedProjection_inputs_assoc]
  · change (leftSmoothMixedAffineLift W b c ha ≫ _) ≫ _ = _
    rw [Category.assoc, leftSmoothAffineOverlapAddition_structure,
      leftSmoothMixedAffineLift_inputs_assoc]

/-- The complete Y/Y chart law respects coefficients, including on the boundary. -/
theorem leftSmoothYAddition_structure :
    leftSmoothYAddition W ≫ integralCurveStructure W =
      (leftSmoothProductChartOpen W true true).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1))) := by
  apply (leftSmoothYCover W).hom_ext
  intro i
  rw [← Category.assoc, leftSmoothYLocal_glued]
  cases i
  · change (leftSmoothYAffineLift W ≫ _) ≫ _ = _
    rw [Category.assoc, leftSmoothAffineOverlapAddition_structure,
      leftSmoothYAffineLift_inputs_assoc]
    rfl
  · change (leftSmoothYProjection W .polynomial ≫ _ ≫ _) ≫ _ = _
    rw [Category.assoc, Category.assoc, leftSmoothPolynomial_structure]
    change leftSmoothYProjection W .polynomial ≫ yProductCoverInclusion W .polynomial ≫ _ = _
    rw [leftSmoothYProjection_inputs_assoc]
  · change (leftSmoothYProjection W .infinity ≫ _ ≫ _) ≫ _ = _
    rw [Category.assoc, Category.assoc, leftSmoothInfinity_structure]
    change leftSmoothYProjection W .infinity ≫ yProductCoverInclusion W .infinity ≫ _ = _
    rw [leftSmoothYProjection_inputs_assoc]

/-- Every enlarged chart law has its original input coefficient morphism. -/
theorem leftSmoothInputAddition_structure (b c : Bool) :
    leftSmoothInputAddition W b c ≫ integralCurveStructure W =
      (leftSmoothProductChartOpen W b c).ι ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))) := by
  cases b <;> cases c
  · exact leftSmoothMixedAddition_structure W false false (.inl rfl)
  · exact leftSmoothMixedAddition_structure W false true (.inl rfl)
  · exact leftSmoothMixedAddition_structure W true false (.inr rfl)
  · exact leftSmoothYAddition_structure W

/-- Each chart law preserves the coefficient map of its actual global input pair. -/
theorem leftSmoothInputAddition_structure_global (b c : Bool) :
    leftSmoothInputAddition W b c ≫ integralCurveStructure W =
      leftSmoothProductChartInput W b c ≫
        pullback.fst (integralCurveStructure W) (integralCurveStructure W) ≫
          integralCurveStructure W := by
  rw [leftSmoothInputAddition_structure, leftSmoothProductChartInput,
    Category.assoc, ← Category.assoc (integralCurveProductChart W b c),
    integralCurveProductChart_fst, Category.assoc, integralCurveChart_structure,
    chartStructure, specAlgHom_structure (chartProductLeft W
      (productChartCoordinate b) (productChartCoordinate c))]

/-- The global enlarged law is over the original coefficient scheme. -/
theorem leftSmoothCurveAddition_structure :
    leftSmoothCurveAddition W ≫ integralCurveStructure W =
      (leftSmoothCurveProductOpen W).ι ≫
        pullback.fst (integralCurveStructure W) (integralCurveStructure W) ≫
          integralCurveStructure W := by
  apply (leftSmoothCurveProductCover W).hom_ext
  rintro ⟨b, c⟩
  rw [← Category.assoc, leftSmoothCurveProductCover_addition, Category.assoc,
    leftSmoothInputAddition_structure_global, leftSmoothCurveProductCoverToChart_inputs_assoc]

end FLT.Mazur.WeierstrassIntegralChart
