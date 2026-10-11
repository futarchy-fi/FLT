/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothTranslationGraph

/-!
# Smoothness and surjectivity of the whole-cubic action

The universal translation isomorphism identifies the action with the second
projection. Smoothness follows from the actual smooth parameter scheme;
surjectivity follows from the proved whole-cubic zero identity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual integral action is smooth, also above singular points of the cubic. -/
instance leftSmoothFactorAddition_smooth : Smooth (leftSmoothFactorAddition W) := by
  rw [← leftSmoothTranslationGraph_snd]
  change Smooth ((leftSmoothTranslationIso W).hom ≫
    pullback.snd (integralSmoothStructure W) (integralCurveStructure W))
  infer_instance

/-- The action is flat as a consequence of its constructed translation isomorphism. -/
theorem leftSmoothFactorAddition_flat : Flat (leftSmoothFactorAddition W) := inferInstance

/-- The original zero graph proves surjectivity of the entire integral action. -/
instance leftSmoothFactorAddition_surjective : Surjective (leftSmoothFactorAddition W) := by
  have h : Surjective (leftSmoothFactorZero W ≫ leftSmoothFactorAddition W) := by
    rw [leftSmoothFactorAddition_left_identity]
    infer_instance
  let _ := h
  exact Surjective.of_comp (leftSmoothFactorZero W) (leftSmoothFactorAddition W)

/-- The universal translation is an isomorphism over its unchanged original smooth parameter. -/
def leftSmoothTranslationOverIso :
    Over.mk (pullback.fst (integralSmoothStructure W) (integralCurveStructure W)) ≅
      Over.mk (pullback.fst (integralSmoothStructure W) (integralCurveStructure W)) where
  hom := Over.homMk (leftSmoothTranslationGraph W) (leftSmoothTranslationGraph_fst W)
  inv := Over.homMk (leftSmoothInverseTranslationGraph W)
    (leftSmoothInverseTranslationGraph_fst W)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    exact leftSmoothTranslationGraph_inv W
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact leftSmoothInverseTranslationGraph_inv W

end FLT.Mazur.WeierstrassIntegralChart
