/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationActionInverse

/-!
# The universal translation and inverse graphs

Both maps retain the original smooth parameter. The second coordinate is the
actual modified translation, or translation by the actual smooth negative.
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

local notation "P" => smoothActionProduct W s b3 b4 b6 h3 h4 h6 hs
local notation "base" =>
  contraction W s b3 b4 b6 h3 h4 h6 hs ≫ integralCurveStructure W
local notation "fst" => pullback.fst (integralSmoothStructure W) base
local notation "snd" => pullback.snd (integralSmoothStructure W) base

/-- Point addition of the original product projections is the actual action morphism. -/
theorem smoothPointAction_projections :
    smoothPointAction W s b3 b4 b6 h3 h4 h6 hs fst snd pullback.condition =
      smoothAction W s b3 b4 b6 h3 h4 h6 hs := by
  rw [smoothPointAction, pullback.lift_fst_snd, Category.id_comp]

/-- The universal translation sends the modified pair `(a,x)` to `(a,a+x)`. -/
def smoothTranslationGraph : P ⟶ P :=
  pullback.lift fst (smoothAction W s b3 b4 b6 h3 h4 h6 hs)
    (smoothAction_structure W s b3 b4 b6 h3 h4 h6 hs).symm

/-- Translation preserves the original smooth parameter. -/
@[reassoc] theorem smoothTranslationGraph_fst :
    smoothTranslationGraph W s b3 b4 b6 h3 h4 h6 hs ≫ fst = fst := pullback.lift_fst _ _ _

/-- Translation uses exactly the constructed whole-modification action. -/
@[reassoc] theorem smoothTranslationGraph_snd :
    smoothTranslationGraph W s b3 b4 b6 h3 h4 h6 hs ≫ snd = smoothAction W s b3 b4 b6 h3 h4 h6 hs :=
  pullback.lift_snd _ _ _

/-- The inverse graph sends the modified pair `(a,x)` to `(a,-a+x)`. -/
def smoothInverseTranslationGraph : P ⟶ P :=
  pullback.lift fst
    (smoothPointAction W s b3 b4 b6 h3 h4 h6 hs (fst ≫ integralSmoothNegation W) snd
      (by rw [Category.assoc, integralSmoothNegation_structure]; exact pullback.condition))
    (by
      change _ = _ ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs
      rw [smoothPointAction_structure, Category.assoc, integralSmoothNegation_structure])

/-- Inverse translation retains the original smooth parameter. -/
@[reassoc] theorem smoothInverseTranslationGraph_fst :
    smoothInverseTranslationGraph W s b3 b4 b6 h3 h4 h6 hs ≫ fst = fst := pullback.lift_fst _ _ _

/-- The inverse graph uses the actual smooth negative to translate the whole cubic. -/
@[reassoc] theorem smoothInverseTranslationGraph_snd :
    smoothInverseTranslationGraph W s b3 b4 b6 h3 h4 h6 hs ≫ snd =
      smoothPointAction W s b3 b4 b6 h3 h4 h6 hs (fst ≫ integralSmoothNegation W) snd
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact pullback.condition) :=
  pullback.lift_snd _ _ _

/-- The inverse translation graph undoes translation on every original scheme-valued pair. -/
theorem smoothTranslationGraph_inv :
    smoothTranslationGraph W s b3 b4 b6 h3 h4 h6 hs ≫
      smoothInverseTranslationGraph W s b3 b4 b6 h3 h4 h6 hs = 𝟙 P := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothInverseTranslationGraph_fst,
      smoothTranslationGraph_fst, Category.id_comp]
  · rw [Category.assoc, smoothInverseTranslationGraph_snd,
      ← smoothPointAction_comp]
    simp only [← Category.assoc, smoothTranslationGraph_fst,
      smoothTranslationGraph_snd, Category.id_comp]
    have he := smoothPointAction_neg_cancel W s b3 b4 b6 h3 h4 h6 hs fst snd pullback.condition
    simpa only [smoothPointAction_projections] using he

/-- Translation also undoes the actual inverse translation graph. -/
theorem smoothInverseTranslationGraph_inv :
    smoothInverseTranslationGraph W s b3 b4 b6 h3 h4 h6 hs ≫
      smoothTranslationGraph W s b3 b4 b6 h3 h4 h6 hs = 𝟙 P := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothTranslationGraph_fst,
      smoothInverseTranslationGraph_fst, Category.id_comp]
  · rw [Category.assoc, smoothTranslationGraph_snd,
      ← smoothPointAction_projections, ← smoothPointAction_comp]
    simp only [smoothInverseTranslationGraph_fst,
      smoothInverseTranslationGraph_snd, Category.id_comp]
    exact smoothPointAction_cancel_neg W s b3 b4 b6 h3 h4 h6 hs fst snd pullback.condition

/-- The whole modified cubic has a universal translation isomorphism over the smooth parameter. -/
def smoothTranslationIso : P ≅ P where
  hom := smoothTranslationGraph W s b3 b4 b6 h3 h4 h6 hs
  inv := smoothInverseTranslationGraph W s b3 b4 b6 h3 h4 h6 hs
  hom_inv_id := smoothTranslationGraph_inv W s b3 b4 b6 h3 h4 h6 hs
  inv_hom_id := smoothInverseTranslationGraph_inv W s b3 b4 b6 h3 h4 h6 hs

end FLT.Mazur.WeierstrassGlobalModification
