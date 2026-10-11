/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationTranslationGraph

/-!
# Smoothness and surjectivity of the entire modified action

The translation isomorphism identifies the action with a smooth projection.
The zero graph splits the action, proving surjectivity on the whole modification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The whole modified action is smooth, including over every exceptional point. -/
instance smoothAction_smooth : Smooth (smoothAction W s b3 b4 b6 h3 h4 h6 hs) := by
  rw [← smoothTranslationGraph_snd]
  change Smooth ((smoothTranslationIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
    pullback.snd (integralSmoothStructure W)
      (contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W))
  infer_instance

/-- Flatness of the action follows from its actual translation isomorphism. -/
theorem smoothAction_flat : Flat (smoothAction W s b3 b4 b6 h3 h4 h6 hs) := inferInstance

/-- The zero graph is an actual section of the entire modified action. -/
def smoothActionZeroGraph : model W s b3 b4 b6 h3 h4 h6 hs ⟶
    smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs :=
  pullback.lift
    (structureMap W s b3 b4 b6 h3 h4 h6 hs ≫ integralSmoothZero W) (𝟙 _)
    (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id,
      Category.id_comp]; rfl)

/-- Acting along the actual zero graph fixes the entire modification. -/
@[reassoc] theorem smoothActionZeroGraph_action :
    smoothActionZeroGraph W s b3 b4 b6 h3 h4 h6 hs ≫
      smoothAction W s b3 b4 b6 h3 h4 h6 hs = 𝟙 _ :=
  smoothPointAction_zero_id W s b3 b4 b6 h3 h4 h6 hs

/-- Every point of the modification lies in the image of the whole action. -/
instance smoothAction_surjective : Surjective (smoothAction W s b3 b4 b6 h3 h4 h6 hs) := by
  have h : Surjective (smoothActionZeroGraph W s b3 b4 b6 h3 h4 h6 hs ≫
      smoothAction W s b3 b4 b6 h3 h4 h6 hs) := by
    rw [smoothActionZeroGraph_action]
    infer_instance
  let _ := h
  exact Surjective.of_comp (smoothActionZeroGraph W s b3 b4 b6 h3 h4 h6 hs)
    (smoothAction W s b3 b4 b6 h3 h4 h6 hs)

/-- Translation is an automorphism over the unchanged original smooth parameter. -/
def smoothTranslationOverIso :
    Over.mk (pullback.fst (integralSmoothStructure W)
      (contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W)) ≅
    Over.mk (pullback.fst (integralSmoothStructure W)
      (contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W)) where
  hom := Over.homMk (smoothTranslationGraph W s b3 b4 b6 h3 h4 h6 hs)
    (smoothTranslationGraph_fst W s b3 b4 b6 h3 h4 h6 hs)
  inv := Over.homMk (smoothInverseTranslationGraph W s b3 b4 b6 h3 h4 h6 hs)
    (smoothInverseTranslationGraph_fst W s b3 b4 b6 h3 h4 h6 hs)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    exact smoothTranslationGraph_inv W s b3 b4 b6 h3 h4 h6 hs
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact smoothInverseTranslationGraph_inv W s b3 b4 b6 h3 h4 h6 hs

end FLT.Mazur.WeierstrassGlobalModification
