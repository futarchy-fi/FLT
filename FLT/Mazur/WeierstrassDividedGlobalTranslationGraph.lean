/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalActionAssociativity

/-!
# Universal translation isomorphisms at every finite depth

The original smooth parameter is retained while translation and its inverse
act on the entire finite model, including its exceptional charts.
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
local notation "P" => finiteGlobalActionProduct hπ data j hj
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst (integralSmoothStructure W) base
local notation "snd" => pullback.snd (integralSmoothStructure W) base

/-- Point addition of the original product projections is the actual action morphism. -/
theorem finiteGlobalPointAction_projections :
    finiteGlobalPointAction hπ data j hj fst snd pullback.condition =
      finiteGlobalAction hπ data j hj := by
  rw [finiteGlobalPointAction, pullback.lift_fst_snd, Category.id_comp]

/-- The universal translation sends the modified pair `(a,x)` to `(a,a+x)`. -/
def finiteGlobalTranslationGraph : P ⟶ P :=
  pullback.lift fst (finiteGlobalAction hπ data j hj)
    (finiteGlobalAction_structure hπ data j hj).symm

/-- Translation preserves the original smooth parameter. -/
@[reassoc] theorem finiteGlobalTranslationGraph_fst :
    finiteGlobalTranslationGraph hπ data j hj ≫ fst = fst :=
  pullback.lift_fst _ _ _

/-- Translation uses exactly the constructed whole-modification action. -/
@[reassoc] theorem finiteGlobalTranslationGraph_snd :
    finiteGlobalTranslationGraph hπ data j hj ≫ snd =
      finiteGlobalAction hπ data j hj :=
  pullback.lift_snd _ _ _

/-- The inverse graph sends the modified pair `(a,x)` to `(a,-a+x)`. -/
def finiteGlobalInverseTranslationGraph : P ⟶ P :=
  pullback.lift fst
    (finiteGlobalPointAction hπ data j hj (fst ≫ integralSmoothNegation W) snd
      (by rw [Category.assoc, integralSmoothNegation_structure]; exact pullback.condition))
    (by
      rw [finiteGlobalPointAction_structure, Category.assoc, integralSmoothNegation_structure])

/-- Inverse translation retains the original smooth parameter. -/
@[reassoc] theorem finiteGlobalInverseTranslationGraph_fst :
    finiteGlobalInverseTranslationGraph hπ data j hj ≫ fst = fst :=
  pullback.lift_fst _ _ _

/-- The inverse graph uses the actual smooth negative to translate the whole cubic. -/
@[reassoc] theorem finiteGlobalInverseTranslationGraph_snd :
    finiteGlobalInverseTranslationGraph hπ data j hj ≫ snd =
      finiteGlobalPointAction hπ data j hj (fst ≫ integralSmoothNegation W) snd
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact pullback.condition) :=
  pullback.lift_snd _ _ _

/-- The inverse translation graph undoes translation on every original scheme-valued pair. -/
theorem finiteGlobalTranslationGraph_inv :
    finiteGlobalTranslationGraph hπ data j hj ≫
      finiteGlobalInverseTranslationGraph hπ data j hj = 𝟙 P := by
  apply pullback.hom_ext
  · rw [Category.assoc, finiteGlobalInverseTranslationGraph_fst,
      finiteGlobalTranslationGraph_fst, Category.id_comp]
  · rw [Category.assoc, finiteGlobalInverseTranslationGraph_snd,
      ← finiteGlobalPointAction_comp]
    simp only [← Category.assoc, finiteGlobalTranslationGraph_fst,
      finiteGlobalTranslationGraph_snd, Category.id_comp]
    have he := finiteGlobalPointAction_neg_cancel hπ data j hj fst snd pullback.condition
    simpa only [finiteGlobalPointAction_projections] using he

/-- Translation also undoes the actual inverse translation graph. -/
theorem finiteGlobalInverseTranslationGraph_inv :
    finiteGlobalInverseTranslationGraph hπ data j hj ≫
      finiteGlobalTranslationGraph hπ data j hj = 𝟙 P := by
  apply pullback.hom_ext
  · rw [Category.assoc, finiteGlobalTranslationGraph_fst,
      finiteGlobalInverseTranslationGraph_fst, Category.id_comp]
  · rw [Category.assoc, finiteGlobalTranslationGraph_snd,
      ← finiteGlobalPointAction_projections, ← finiteGlobalPointAction_comp]
    simp only [finiteGlobalInverseTranslationGraph_fst,
      finiteGlobalInverseTranslationGraph_snd, Category.id_comp]
    exact finiteGlobalPointAction_cancel_neg hπ data j hj fst snd pullback.condition

/-- The whole modified cubic has a universal translation isomorphism over the smooth parameter. -/
def finiteGlobalTranslationIso : P ≅ P where
  hom := finiteGlobalTranslationGraph hπ data j hj
  inv := finiteGlobalInverseTranslationGraph hπ data j hj
  hom_inv_id := finiteGlobalTranslationGraph_inv hπ data j hj
  inv_hom_id := finiteGlobalInverseTranslationGraph_inv hπ data j hj

end FLT.Mazur.WeierstrassDividedDepth
