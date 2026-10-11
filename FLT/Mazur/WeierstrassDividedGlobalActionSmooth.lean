/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTranslationGraph

/-!
# Smoothness and surjectivity of every finite global action

Translation identifies each whole action with a smooth projection. The
original zero section gives an actual splitting at every finite depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

variable (j : ℕ) (hj : j ≤ n)
/-- The whole modified action is smooth, including over every exceptional point. -/
instance finiteGlobalAction_smooth : Smooth (finiteGlobalAction hπ data j hj) := by
  rw [← finiteGlobalTranslationGraph_snd]
  change Smooth ((finiteGlobalTranslationIso hπ data j hj).hom ≫
    pullback.snd (integralSmoothStructure W)
      (finiteGlobalStructure hπ data j hj))
  infer_instance

/-- Flatness of the action follows from its actual translation isomorphism. -/
theorem finiteGlobalAction_flat : Flat (finiteGlobalAction hπ data j hj) := inferInstance

/-- The zero graph is an actual section of the entire modified action. -/
def finiteGlobalActionZeroGraph : finiteGlobalModel hπ data j hj ⟶
    finiteGlobalActionProduct hπ data j hj :=
  pullback.lift
    (finiteGlobalStructure hπ data j hj ≫ integralSmoothZero W) (𝟙 _)
    (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id,
      Category.id_comp])

/-- Acting along the actual zero graph fixes the entire modification. -/
@[reassoc] theorem finiteGlobalActionZeroGraph_action :
    finiteGlobalActionZeroGraph hπ data j hj ≫
      finiteGlobalAction hπ data j hj = 𝟙 _ := by
  simpa only [finiteGlobalPointAction, finiteGlobalActionZeroGraph, Category.id_comp] using
    finiteGlobalPointAction_zero hπ data j hj (𝟙 _)

/-- Every point of the modification lies in the image of the whole action. -/
instance finiteGlobalAction_surjective : Surjective (finiteGlobalAction hπ data j hj) := by
  have h : Surjective (finiteGlobalActionZeroGraph hπ data j hj ≫
      finiteGlobalAction hπ data j hj) := by
    rw [finiteGlobalActionZeroGraph_action]
    infer_instance
  let _ := h
  exact Surjective.of_comp (finiteGlobalActionZeroGraph hπ data j hj)
    (finiteGlobalAction hπ data j hj)

/-- Translation is an automorphism over the unchanged original smooth parameter. -/
def finiteGlobalTranslationOverIso :
    Over.mk (pullback.fst (integralSmoothStructure W)
      (finiteGlobalStructure hπ data j hj)) ≅
    Over.mk (pullback.fst (integralSmoothStructure W)
      (finiteGlobalStructure hπ data j hj)) where
  hom := Over.homMk (finiteGlobalTranslationGraph hπ data j hj)
    (finiteGlobalTranslationGraph_fst hπ data j hj)
  inv := Over.homMk (finiteGlobalInverseTranslationGraph hπ data j hj)
    (finiteGlobalInverseTranslationGraph_fst hπ data j hj)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    exact finiteGlobalTranslationGraph_inv hπ data j hj
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact finiteGlobalInverseTranslationGraph_inv hπ data j hj

end FLT.Mazur.WeierstrassDividedDepth
