/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedSmoothAction

/-!
# Action laws on every resolved smooth component

The full smooth-open restriction inherits zero, inverse and associativity
from the constructed whole-model action, through its monomorphic inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The original zero fixes all resolved smooth scheme-valued points. -/
theorem finiteGlobalSmoothPointAction_zero {T : Scheme.{u}} (b : T ⟶ (U).toScheme) :
    finiteGlobalSmoothPointAction hπ data j hj
      (b ≫ (U).ι ≫ base ≫ integralSmoothZero W) b
      (by rw [Category.assoc, Category.assoc, Category.assoc,
        integralSmoothZero_structure, Category.comp_id]) = b := by
  apply (cancel_mono (U).ι).mp
  rw [finiteGlobalSmoothPointAction_inclusion]
  simpa only [Category.assoc] using
    finiteGlobalPointAction_zero hπ data j hj (b ≫ (U).ι)

/-- Negative original translation cancels on the entire resolved smooth open. -/
theorem finiteGlobalSmoothPointAction_neg_cancel {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ (U).ι ≫ base) :
    finiteGlobalSmoothPointAction hπ data j hj (a ≫ integralSmoothNegation W)
      (finiteGlobalSmoothPointAction hπ data j hj a b h)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        finiteGlobalSmoothPointAction_structure]) = b := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalSmoothPointAction_inclusion]
  exact finiteGlobalPointAction_neg_cancel hπ data j hj a (b ≫ (U).ι)
    (by simpa only [Category.assoc] using h)

/-- Translation also cancels its negative on every resolved smooth test point. -/
theorem finiteGlobalSmoothPointAction_cancel_neg {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ (U).ι ≫ base) :
    finiteGlobalSmoothPointAction hπ data j hj a
      (finiteGlobalSmoothPointAction hπ data j hj (a ≫ integralSmoothNegation W) b
        (by rw [Category.assoc, integralSmoothNegation_structure]; exact h))
      (by rw [finiteGlobalSmoothPointAction_structure, Category.assoc,
        integralSmoothNegation_structure]) = b := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalSmoothPointAction_inclusion]
  exact finiteGlobalPointAction_cancel_neg hπ data j hj a (b ≫ (U).ι)
    (by simpa only [Category.assoc] using h)

/-- Original addition acts associatively on every resolved smooth component. -/
theorem finiteGlobalSmoothPointAction_assoc {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen W).toScheme) (c : T ⟶ (U).toScheme)
    (hab : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W)
    (hbc : b ≫ integralSmoothStructure W = c ≫ (U).ι ≫ base) :
    finiteGlobalSmoothPointAction hπ data j hj (smoothPairPointAddition W a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) =
      finiteGlobalSmoothPointAction hπ data j hj a
        (finiteGlobalSmoothPointAction hπ data j hj b c hbc)
        (by rw [finiteGlobalSmoothPointAction_structure]; exact hab) := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalSmoothPointAction_inclusion]
  exact finiteGlobalPointAction_assoc hπ data j hj a b (c ≫ (U).ι) hab
    (by simpa only [Category.assoc] using hbc)

end FLT.Mazur.WeierstrassDividedDepth
