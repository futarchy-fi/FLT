/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalInitialActionLaws
public import FLT.Mazur.WeierstrassDividedGlobalPointAction
public import FLT.Mazur.WeierstrassDividedGlobalStepFlatExt

/-!
# Identity law on every whole finite model

Flat-reference uniqueness proves the identity at the universal model
point. Naturality then gives the identity on every scheme-valued point,
without requiring that point to be flat.
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

/-- The point action at depth zero is the transported whole initial point action. -/
theorem finiteGlobalPointAction_zero_stage {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (h : a ≫ integralSmoothStructure W = b ≫ finiteGlobalStructure hπ data 0 (Nat.zero_le n)) :
    finiteGlobalPointAction hπ data 0 (Nat.zero_le n) a b h =
      finiteGlobalInitialPointAction hπ data a b h := by
  simp only [finiteGlobalPointAction, finiteGlobalAction_zero, finiteGlobalInitialAction,
    ← finiteGlobalInitialPointAction_comp, pullback.lift_fst, pullback.lift_snd]

/-- The original smooth zero fixes every point of every finite global model. -/
theorem finiteGlobalPointAction_zero (j : ℕ) (hj : j ≤ n) {T : Scheme.{u}}
    (b : T ⟶ finiteGlobalModel hπ data j hj) :
    finiteGlobalPointAction hπ data j hj
      (b ≫ finiteGlobalStructure hπ data j hj ≫ integralSmoothZero W) b
      (by rw [Category.assoc, Category.assoc, integralSmoothZero_structure,
        Category.comp_id]) = b := by
  induction j generalizing T with
  | zero =>
    rw [finiteGlobalPointAction_zero_stage, finiteGlobalInitialPointAction_zero]
  | succ j ih =>
    let base := finiteGlobalStructure hπ data (j + 1) hj
    have hid : finiteGlobalPointAction hπ data (j + 1) hj
        (base ≫ integralSmoothZero W) (𝟙 _)
        (by rw [Category.assoc, integralSmoothZero_structure,
          Category.comp_id, Category.id_comp]) = 𝟙 _ := by
      apply finiteGlobalStep_ext_of_flat hπ data j hj (𝟙 _)
      simp only [finiteGlobalPointAction_step, Category.id_comp]
      have hz : base ≫ integralSmoothZero W =
          finiteGlobalStep hπ data j hj ≫
            finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj) ≫ integralSmoothZero W := by
        rw [finiteGlobalStep_structure_assoc]
      simp only [hz]
      exact ih (Nat.le_of_succ_le hj) (finiteGlobalStep hπ data j hj)
    have he := congrArg (fun f => b ≫ f) hid
    rw [← finiteGlobalPointAction_comp] at he
    simpa only [Category.comp_id, Category.assoc] using he

end FLT.Mazur.WeierstrassDividedDepth
