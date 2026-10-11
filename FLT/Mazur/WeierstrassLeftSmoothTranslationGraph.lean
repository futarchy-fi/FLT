/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# The universal translation and inverse graphs

Both maps retain the original smooth parameter. The second coordinate is the
actual integral translation, or translation by the actual smooth negative.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

local notation "P" => leftSmoothFactorProduct W
local notation "fst" => pullback.fst (integralSmoothStructure W) (integralCurveStructure W)
local notation "snd" => pullback.snd (integralSmoothStructure W) (integralCurveStructure W)

/-- Point addition of the original product projections is the actual action morphism. -/
theorem leftSmoothPointAddition_projections :
    leftSmoothPointAddition W fst snd pullback.condition = leftSmoothFactorAddition W := by
  rw [leftSmoothPointAddition, pullback.lift_fst_snd, Category.id_comp]

/-- The universal translation sends the original pair `(a,x)` to `(a,a+x)`. -/
def leftSmoothTranslationGraph : P ⟶ P :=
  pullback.lift fst (leftSmoothFactorAddition W) (leftSmoothFactorAddition_structure W).symm

/-- Translation preserves the original smooth parameter. -/
@[reassoc] theorem leftSmoothTranslationGraph_fst :
    leftSmoothTranslationGraph W ≫ fst = fst := pullback.lift_fst _ _ _

/-- Translation uses exactly the constructed whole-cubic action. -/
@[reassoc] theorem leftSmoothTranslationGraph_snd :
    leftSmoothTranslationGraph W ≫ snd = leftSmoothFactorAddition W := pullback.lift_snd _ _ _

/-- The inverse graph sends the original pair `(a,x)` to `(a,-a+x)`. -/
def leftSmoothInverseTranslationGraph : P ⟶ P :=
  pullback.lift fst
    (leftSmoothPointAddition W (fst ≫ integralSmoothNegation W) snd
      (by rw [Category.assoc, integralSmoothNegation_structure]; exact pullback.condition))
    (by rw [leftSmoothPointAddition_structure, Category.assoc, integralSmoothNegation_structure])

/-- Inverse translation retains the original smooth parameter. -/
@[reassoc] theorem leftSmoothInverseTranslationGraph_fst :
    leftSmoothInverseTranslationGraph W ≫ fst = fst := pullback.lift_fst _ _ _

/-- The inverse graph uses the actual smooth negative to translate the whole cubic. -/
@[reassoc] theorem leftSmoothInverseTranslationGraph_snd :
    leftSmoothInverseTranslationGraph W ≫ snd =
      leftSmoothPointAddition W (fst ≫ integralSmoothNegation W) snd
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact pullback.condition) :=
  pullback.lift_snd _ _ _

/-- The inverse translation graph undoes translation on every original scheme-valued pair. -/
theorem leftSmoothTranslationGraph_inv :
    leftSmoothTranslationGraph W ≫ leftSmoothInverseTranslationGraph W = 𝟙 P := by
  apply pullback.hom_ext
  · rw [Category.assoc, leftSmoothInverseTranslationGraph_fst,
      leftSmoothTranslationGraph_fst, Category.id_comp]
  · rw [Category.assoc, leftSmoothInverseTranslationGraph_snd,
      ← leftSmoothPointAddition_comp]
    simp only [← Category.assoc, leftSmoothTranslationGraph_fst,
      leftSmoothTranslationGraph_snd, Category.id_comp]
    have he := leftSmoothPointAddition_neg_cancel W fst snd pullback.condition
    simpa only [leftSmoothPointAddition_projections] using he

/-- Translation also undoes the actual inverse translation graph. -/
theorem leftSmoothInverseTranslationGraph_inv :
    leftSmoothInverseTranslationGraph W ≫ leftSmoothTranslationGraph W = 𝟙 P := by
  apply pullback.hom_ext
  · rw [Category.assoc, leftSmoothTranslationGraph_fst,
      leftSmoothInverseTranslationGraph_fst, Category.id_comp]
  · rw [Category.assoc, leftSmoothTranslationGraph_snd,
      ← leftSmoothPointAddition_projections, ← leftSmoothPointAddition_comp]
    simp only [leftSmoothInverseTranslationGraph_fst,
      leftSmoothInverseTranslationGraph_snd, Category.id_comp]
    exact leftSmoothPointAddition_cancel_neg W fst snd pullback.condition

/-- The whole original cubic has a universal translation isomorphism over the smooth parameter. -/
def leftSmoothTranslationIso : P ≅ P where
  hom := leftSmoothTranslationGraph W
  inv := leftSmoothInverseTranslationGraph W
  hom_inv_id := leftSmoothTranslationGraph_inv W
  inv_hom_id := leftSmoothInverseTranslationGraph_inv W

end FLT.Mazur.WeierstrassIntegralChart
