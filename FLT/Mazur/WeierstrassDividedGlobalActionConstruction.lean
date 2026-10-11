/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalInitialAction
public import FLT.Mazur.WeierstrassDividedSuccessorGlobalAction

/-!
# Constructing whole action maps at every finite depth

Starting with the actual initial action, the successor construction builds
compatible maps on every finite global model. Their original contractions
and coefficient morphisms are proved as part of the construction.
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

/-- A recursively constructed map and its proved original-action contraction. -/
def finiteGlobalActionConstruction : (j : ℕ) → (hj : j ≤ n) →
    {a : finiteGlobalActionProduct hπ data j hj ⟶ finiteGlobalModel hπ data j hj //
      a ≫ finiteGlobalContraction hπ data j hj =
        finiteGlobalActionInput hπ data j hj ≫ leftSmoothFactorAddition W}
  | 0, _ => ⟨finiteGlobalInitialAction hπ data, finiteGlobalInitialAction_contraction hπ data⟩
  | j + 1, hj =>
    let prev := finiteGlobalActionConstruction j (Nat.le_of_succ_le hj)
    ⟨successorGlobalAction hπ data j hj prev.val prev.property,
      successorGlobalAction_original hπ data j hj prev.val prev.property⟩

/-- The whole smooth-input action map on each actual finite global model. -/
def finiteGlobalAction (j : ℕ) (hj : j ≤ n) :
    finiteGlobalActionProduct hπ data j hj ⟶ finiteGlobalModel hπ data j hj :=
  (finiteGlobalActionConstruction hπ data j hj).val

/-- Every finite action contracts to exactly the genuine original smooth addition. -/
@[reassoc] theorem finiteGlobalAction_contraction (j : ℕ) (hj : j ≤ n) :
    finiteGlobalAction hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      finiteGlobalActionInput hπ data j hj ≫ leftSmoothFactorAddition W :=
  (finiteGlobalActionConstruction hπ data j hj).property

/-- Stage zero recovers the transported initial action. -/
@[simp] theorem finiteGlobalAction_zero :
    finiteGlobalAction hπ data 0 (Nat.zero_le n) = finiteGlobalInitialAction hπ data := rfl

/-- Each successor map is the actual lift of its preceding constructed map. -/
theorem finiteGlobalAction_succ (j : ℕ) (hj : j + 1 ≤ n) :
    finiteGlobalAction hπ data (j + 1) hj =
      successorGlobalAction hπ data j hj
        (finiteGlobalAction hπ data j (Nat.le_of_succ_le hj))
        (finiteGlobalAction_contraction hπ data j (Nat.le_of_succ_le hj)) := rfl

/-- Step contraction preserves the smooth parameter and the preceding action. -/
@[reassoc] theorem finiteGlobalAction_step (j : ℕ) (hj : j + 1 ≤ n) :
    finiteGlobalAction hπ data (j + 1) hj ≫ finiteGlobalStep hπ data j hj =
      successorActionInput hπ data j hj ≫
        finiteGlobalAction hπ data j (Nat.le_of_succ_le hj) := by
  rw [finiteGlobalAction_succ, successorGlobalAction_step]
  rfl

/-- Every constructed action lies over its original coefficient scheme. -/
@[reassoc] theorem finiteGlobalAction_structure (j : ℕ) (hj : j ≤ n) :
    finiteGlobalAction hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      pullback.fst _ _ ≫ integralSmoothStructure W := by
  change finiteGlobalAction hπ data j hj ≫
    finiteGlobalContraction hπ data j hj ≫ integralCurveStructure W = _
  rw [finiteGlobalAction_contraction_assoc,
    leftSmoothFactorAddition_structure, finiteGlobalActionInput_fst_assoc]

/-- The maps recover the original smooth-input actions at every finite depth. -/
@[reassoc] theorem finiteGlobalAction_originalSmooth (j : ℕ) (hj : j ≤ n) :
    finiteGlobalOriginalSmoothPair hπ data j hj ≫ finiteGlobalAction hπ data j hj =
      finiteGlobalOriginalSmoothAction hπ data j hj :=
  finiteGlobalAction_originalSmooth_unique hπ data j hj
    (finiteGlobalAction hπ data j hj) (finiteGlobalAction_contraction hπ data j hj)

end FLT.Mazur.WeierstrassDividedDepth
