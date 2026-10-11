/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCharts
public import FLT.Mazur.WeierstrassDividedGlobalFiniteActionProduct

/-!
# Action inputs and preceding-stage outputs at every finite successor

Contract only the second input of the whole successor product. Composing
with any constructed preceding action supplies the exact output to lift.
Original-action compatibility propagates from the preceding stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)

/-- The whole successor input, with its smooth parameter unchanged. -/
def successorActionInput : finiteGlobalActionProduct hπ data (j + 1) hj ⟶
    finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ finiteGlobalStep hπ data j hj)
    (by rw [Category.assoc, finiteGlobalStep_structure]; exact pullback.condition)

/-- The first projection retains the original smooth parameter. -/
@[reassoc] theorem successorActionInput_fst :
    successorActionInput hπ data j hj ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second projection contracts the actual successor finite model. -/
@[reassoc] theorem successorActionInput_snd :
    successorActionInput hπ data j hj ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finiteGlobalStep hπ data j hj := pullback.lift_snd _ _ _

variable (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
  finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))

/-- The preceding action pulled back to the complete successor input. -/
def successorActionOutput : finiteGlobalActionProduct hπ data (j + 1) hj ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj) :=
  successorActionInput hπ data j hj ≫ a

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)

include ha
/-- The pulled-back output contracts to the prescribed original action. -/
@[reassoc] theorem successorActionOutput_contraction :
    successorActionOutput hπ data j hj a ≫
        finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
      finiteGlobalActionInput hπ data (j + 1) hj ≫ leftSmoothFactorAddition W := by
  rw [successorActionOutput, Category.assoc, ha,
    ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, finiteGlobalActionInput_fst, successorActionInput_fst,
      finiteGlobalActionInput_fst]
  · rw [Category.assoc, finiteGlobalActionInput_snd, successorActionInput_snd_assoc,
      finiteGlobalStep_contraction, finiteGlobalActionInput_snd]

/-- The actual output remains over the smooth parameter's coefficient map. -/
@[reassoc] theorem successorActionOutput_structure :
    successorActionOutput hπ data j hj a ≫ finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj) =
      pullback.fst _ _ ≫ integralSmoothStructure W := by
  rw [finiteGlobalStructure, successorActionOutput_contraction_assoc hπ data j hj a ha,
    leftSmoothFactorAddition_structure, finiteGlobalActionInput_fst_assoc]

end FLT.Mazur.WeierstrassDividedDepth
