/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCharts
public import FLT.Mazur.WeierstrassDividedGlobalInitialActionLaws

/-!
# Pulling the actual initial action back along the first whole successor

The source is the smooth parameter times the entire first finite model.
Contract only the second input to stage zero, then apply the already
constructed initial action. This supplies the output map to be lifted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

/-- The first whole successor input, with its smooth parameter unchanged. -/
def firstActionInput : finiteGlobalActionProduct hπ data 1 hn ⟶
    finiteGlobalActionProduct hπ data 0 (Nat.zero_le n) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ finiteGlobalStep hπ data 0 hn)
    (by rw [Category.assoc, finiteGlobalStep_structure]; exact pullback.condition)

/-- The first projection retains the original smooth parameter. -/
@[reassoc] theorem firstActionInput_fst :
    firstActionInput hπ data hn ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second projection contracts the actual first finite model. -/
@[reassoc] theorem firstActionInput_snd :
    firstActionInput hπ data hn ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finiteGlobalStep hπ data 0 hn := pullback.lift_snd _ _ _

/-- The actual initial action pulled back to the complete first successor input. -/
def firstActionOutput : finiteGlobalActionProduct hπ data 1 hn ⟶
    finiteGlobalModel hπ data 0 (Nat.zero_le n) :=
  firstActionInput hπ data hn ≫ finiteGlobalInitialAction hπ data

/-- The pulled-back output contracts to the prescribed original action. -/
@[reassoc] theorem firstActionOutput_contraction :
    firstActionOutput hπ data hn ≫ finiteGlobalContraction hπ data 0 (Nat.zero_le n) =
      finiteGlobalActionInput hπ data 1 hn ≫ leftSmoothFactorAddition W := by
  rw [firstActionOutput, Category.assoc, finiteGlobalInitialAction_contraction,
    ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, finiteGlobalActionInput_fst, firstActionInput_fst,
      finiteGlobalActionInput_fst]
  · rw [Category.assoc, finiteGlobalActionInput_snd, firstActionInput_snd_assoc,
      finiteGlobalStep_contraction, finiteGlobalActionInput_snd]

/-- The actual output remains over the smooth parameter's coefficient map. -/
@[reassoc] theorem firstActionOutput_structure :
    firstActionOutput hπ data hn ≫ finiteGlobalStructure hπ data 0 (Nat.zero_le n) =
      pullback.fst _ _ ≫ integralSmoothStructure W := by
  rw [finiteGlobalStructure, firstActionOutput_contraction_assoc,
    leftSmoothFactorAddition_structure, finiteGlobalActionInput_fst_assoc]

end FLT.Mazur.WeierstrassDividedDepth
