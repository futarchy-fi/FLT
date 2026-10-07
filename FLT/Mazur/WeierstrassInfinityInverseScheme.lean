/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInverseNeighborhood

/-!
# The global inverse identity on the infinity neighborhood

The explicit input map is the restriction of the constructed point-negation
section of the actual curve product. Its zero output therefore gives the inverse
identity for global addition on this entire open neighborhood.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] infinityInverseDen infinityInverseOutputY

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The normalized pair is the actual global right-negation section on this open. -/
theorem infinityNegationInput_spec :
    Spec.map (CommRingCat.ofHom (infinityNegationInput W).toRingHom) ≫
        integralCurveProductChart W true true =
      infinityNegationInclusion W ≫ integralCurveChart W 1 ≫ integralCurveRightNegation W := by
  apply pullback.hom_ext
  · rw [Category.assoc, integralCurveProductChart_fst, Category.assoc, Category.assoc,
      integralCurveRightNegation_fst, Category.comp_id, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (((infinityNegationInput W).comp (chartProductLeft W 1 1)).toRingHom)) ≫ _ = _
    rw [infinityNegationInput_left]
    rfl
  · rw [Category.assoc, integralCurveProductChart_snd, Category.assoc, Category.assoc,
      integralCurveRightNegation_snd, integralCurveChart_negation_infinity,
      ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (((infinityNegationInput W).comp (chartProductRight W 1 1)).toRingHom)) ≫ _ = _
    rw [infinityNegationInput_right]
    rfl

/-- The inverse neighborhood factors through the original negation neighborhood. -/
theorem infinityInverseInclusion_factor :
    infinityInverseInclusion W =
      Spec.map (CommRingCat.ofHom (infinityInverseNegationRestriction W).toRingHom) ≫
        infinityNegationInclusion W := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The original infinity addition domain receives exactly the same inverse pair. -/
theorem infinityInverseSpec_inputs :
    Spec.map (CommRingCat.ofHom (infinityInverseMap W).toRingHom) ≫
        infinityAdditionInclusion W =
      Spec.map (CommRingCat.ofHom (infinityInverseNegationRestriction W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (infinityNegationInput W).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityInverseMap_inputs W)

/-- The normalized output is the base-valued zero section as an actual scheme morphism. -/
theorem infinityInverseSpec_addition :
    Spec.map (CommRingCat.ofHom (infinityInverseMap W).toRingHom) ≫
        infinityAdditionSpec W ≫ integralCurveChart W 1 =
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityInverseOpen W))) ≫
        integralCurveZero W := by
  rw [← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((infinityInverseMap W).comp (infinityAdditionChart W)).toRingHom)) ≫ _ = _
  rw [infinityInverseMap_addition, integralCurveZero, ← Category.assoc, ← Spec.map_comp,
    chartInfinityEvaluation_base]
  rfl

/-- Global addition has the inverse identity on the constructed infinity neighborhood. -/
theorem integralCurveAddition_rightNegation_neighborhood (hΔ : IsUnit W.Δ) :
    infinityInverseInclusion W ≫ integralCurveChart W 1 ≫
        integralCurveRightNegation W ≫ integralCurveAddition W hΔ =
      infinityInverseInclusion W ≫ integralCurveChart W 1 ≫
        integralCurveStructure W ≫ integralCurveZero W := by
  have hs : infinityInverseInclusion W ≫ integralCurveChart W 1 ≫
      integralCurveRightNegation W =
      Spec.map (CommRingCat.ofHom (infinityInverseMap W).toRingHom) ≫
        infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
    rw [infinityInverseInclusion_factor, Category.assoc, ← infinityNegationInput_spec,
      ← Category.assoc, ← infinityInverseSpec_inputs, Category.assoc]
  rw [← Category.assoc (infinityInverseInclusion W),
    ← Category.assoc (infinityInverseInclusion W ≫ integralCurveChart W 1)]
  rw [Category.assoc (infinityInverseInclusion W) (integralCurveChart W 1), hs]
  rw [Category.assoc, Category.assoc, integralCurveProductChart_addition]
  change Spec.map _ ≫ infinityAdditionInclusion W ≫ yProductAdditionToCurve W hΔ = _
  rw [yProductAdditionToCurve_infinity, infinityInverseSpec_addition,
    ← Category.assoc (integralCurveChart W 1), integralCurveChart_structure,
    chartStructure, ← Category.assoc]
  exact congrArg (fun t => t ≫ integralCurveZero W)
    (specAlgHom_structure (infinityInverseRestriction W)).symm

end FLT.Mazur.WeierstrassIntegralChart
