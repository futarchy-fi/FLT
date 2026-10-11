/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientAction
public import FLT.Mazur.WeierstrassSmoothCoefficientPointAddition

/-!
# Intrinsic action laws after arbitrary coefficient extension

The constructed action on the tensor model uses the original zero, inverse
and addition over the extended ring. Its laws hold on every test scheme.
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
  (j : ℕ) (hj : j ≤ n) (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst q base
local notation "snd" => pullback.snd q base

/-- The actual extended zero fixes every point on the whole tensor model. -/
theorem finiteGlobalCoefficientPointAction_zero {T : Scheme.{u}}
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj) :
    finiteGlobalCoefficientPointAction hπ data j hj S
      (b ≫ fst ≫ integralSmoothZero V) b
      (by rw [Category.assoc, Category.assoc, integralSmoothZero_structure,
        Category.comp_id]) = b := by
  apply pullback.hom_ext
  · rw [finiteGlobalCoefficientPointAction_structure, Category.assoc, Category.assoc,
      integralSmoothZero_structure, Category.comp_id]
  · rw [finiteGlobalCoefficientPointAction_projection]
    have hz : (b ≫ fst ≫ integralSmoothZero V) ≫ originalSmoothCoefficientMap S W =
        (b ≫ snd) ≫ base ≫ integralSmoothZero W := by
      rw [Category.assoc, Category.assoc, originalSmoothCoefficientMap_zero,
        ← Category.assoc fst, pullback.condition, Category.assoc, Category.assoc]
    simp only [hz]
    exact finiteGlobalPointAction_zero hπ data j hj (b ≫ snd)

/-- The actual extended inverse cancels translation on every tensor-model point. -/
theorem finiteGlobalCoefficientPointAction_neg_cancel {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    finiteGlobalCoefficientPointAction hπ data j hj S (a ≫ integralSmoothNegation V)
      (finiteGlobalCoefficientPointAction hπ data j hj S a b h)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        finiteGlobalCoefficientPointAction_structure]) = b := by
  apply pullback.hom_ext
  · rw [finiteGlobalCoefficientPointAction_structure, Category.assoc,
      integralSmoothNegation_structure, h]
  · rw [finiteGlobalCoefficientPointAction_projection]
    have hn : (a ≫ integralSmoothNegation V) ≫ originalSmoothCoefficientMap S W =
        (a ≫ originalSmoothCoefficientMap S W) ≫ integralSmoothNegation W := by
      rw [Category.assoc, originalSmoothCoefficientMap_negation, Category.assoc]
    have hp := finiteGlobalCoefficientPointAction_projection hπ data j hj S a b h
    simp only [hn, hp]
    exact finiteGlobalPointAction_neg_cancel hπ data j hj
      (a ≫ originalSmoothCoefficientMap S W) (b ≫ snd) _

/-- Translation also cancels the intrinsic negative parameter on every extended point. -/
theorem finiteGlobalCoefficientPointAction_cancel_neg {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    finiteGlobalCoefficientPointAction hπ data j hj S a
      (finiteGlobalCoefficientPointAction hπ data j hj S (a ≫ integralSmoothNegation V) b
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact h))
      (by rw [finiteGlobalCoefficientPointAction_structure, Category.assoc,
        integralSmoothNegation_structure]) = b := by
  have he := finiteGlobalCoefficientPointAction_neg_cancel hπ data j hj S
    (a ≫ integralSmoothNegation V) b
    (by rw [Category.assoc, integralSmoothNegation_structure]; exact h)
  simpa only [Category.assoc, integralSmoothNegation_comp, Category.comp_id] using he

/-- Addition intrinsic to the extended smooth curve acts associatively on the tensor model. -/
theorem finiteGlobalCoefficientPointAction_assoc {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen V).toScheme)
    (c : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (hab : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V)
    (hbc : b ≫ integralSmoothStructure V = c ≫ fst) :
    finiteGlobalCoefficientPointAction hπ data j hj S (smoothPairPointAddition V a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) =
      finiteGlobalCoefficientPointAction hπ data j hj S a
        (finiteGlobalCoefficientPointAction hπ data j hj S b c hbc)
        (by rw [finiteGlobalCoefficientPointAction_structure]; exact hab) := by
  apply pullback.hom_ext
  · simp only [finiteGlobalCoefficientPointAction_structure, smoothPairPointAddition_structure]
  · simp only [finiteGlobalCoefficientPointAction_projection,
      originalSmoothCoefficientMap_pointAddition]
    exact finiteGlobalPointAction_assoc hπ data j hj
      (a ≫ originalSmoothCoefficientMap S W) (b ≫ originalSmoothCoefficientMap S W)
      (c ≫ snd) _ _

end FLT.Mazur.WeierstrassDividedDepth
