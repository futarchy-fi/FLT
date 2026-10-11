/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorDividedAction
public import FLT.Mazur.WeierstrassDividedSuccessorExteriorAction
public import FLT.Mazur.WeierstrassDividedSuccessorInfinityAction
public import FLT.Mazur.WeierstrassDividedSuccessorOutputCover

/-!
# The action on the entire finite successor

Glue the constructed infinity, exterior, and divided output actions on
their full intersections. The resulting map retains the exact global step
and the genuine original smooth action on the whole source product.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))
  (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
    finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)

local notation "C" => successorActionOutputCover hπ data j hj a

/-- The constructed action on every output branch of the whole successor source. -/
def successorOutputBranchAction (k : Option Bool) :
    (C).X k ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  match k with
  | none => successorInfinityOutputAction hπ data j hj a
  | some false => successorExteriorOutputAction hπ data j hj a
  | some true => successorDividedAction hπ data j hj a ha

/-- All output branches retain exactly the existing preceding-action output. -/
@[reassoc] theorem successorOutputBranchAction_step (k : Option Bool) :
    successorOutputBranchAction hπ data j hj a ha k ≫ finiteGlobalStep hπ data j hj =
      (C).f k ≫ successorActionOutput hπ data j hj a := by
  rcases k with _ | (_ | _)
  · exact successorInfinityOutputAction_step hπ data j hj a
  · exact successorExteriorOutputAction_step hπ data j hj a
  · exact successorDividedAction_output hπ data j hj a ha

/-- Each output branch is uniquely characterized after every flat scheme restriction. -/
theorem successorOutputBranchAction_flat_unique (k : Option Bool) {T : Scheme.{u}}
    (p : T ⟶ (C).X k) [Flat p] (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorOutputBranchAction hπ data j hj a ha k ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorOutputBranchAction hπ data j hj a ha k := by
  rcases k with _ | (_ | _)
  · apply successorInfinityOutputAction_unique hπ data j hj a p b
    simpa only [successorOutputBranchAction, successorInfinityOutputAction_step] using hb
  · apply successorExteriorOutputAction_unique hπ data j hj a p b
    simpa only [successorOutputBranchAction, successorExteriorOutputAction_step] using hb
  · exact successorDividedAction_flat_unique hπ data j hj a ha p b hb

/-- The actual output actions agree on all complete scheme-theoretic intersections. -/
theorem successorOutputBranchAction_overlap (i k : Option Bool) :
    pullback.fst ((C).f i) ((C).f k) ≫ successorOutputBranchAction hπ data j hj a ha i =
      pullback.snd ((C).f i) ((C).f k) ≫ successorOutputBranchAction hπ data j hj a ha k := by
  symm
  apply successorOutputBranchAction_flat_unique hπ data j hj a ha i
    (pullback.fst ((C).f i) ((C).f k))
  simp only [Category.assoc, successorOutputBranchAction_step]
  rw [pullback.condition_assoc]

/-- The genuine action map on the whole successor model. -/
irreducible_def successorGlobalAction : finiteGlobalActionProduct hπ data (j + 1) hj ⟶
    finiteGlobalModel hπ data (j + 1) hj :=
  (C).glueMorphisms (successorOutputBranchAction hπ data j hj a ha)
    (successorOutputBranchAction_overlap hπ data j hj a ha)

/-- The whole action restricts to each of the constructed output actions. -/
@[reassoc] theorem successorGlobalAction_branch (k : Option Bool) :
    (C).f k ≫ successorGlobalAction hπ data j hj a ha =
      successorOutputBranchAction hπ data j hj a ha k := by
  rw [successorGlobalAction_def]
  exact (C).ι_glueMorphisms _ _ k

/-- The whole successor action contracts to precisely the preceding action. -/
@[reassoc] theorem successorGlobalAction_step :
    successorGlobalAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj =
      successorActionOutput hπ data j hj a := by
  apply (C).hom_ext
  intro k
  rw [successorGlobalAction_branch_assoc, successorOutputBranchAction_step]

/-- The entire action preserves the actual original input pair and smooth addition. -/
@[reassoc] theorem successorGlobalAction_original :
    successorGlobalAction hπ data j hj a ha ≫ finiteGlobalContraction hπ data (j + 1) hj =
      finiteGlobalActionInput hπ data (j + 1) hj ≫ leftSmoothFactorAddition W := by
  rw [← finiteGlobalStep_contraction hπ data j hj, successorGlobalAction_step_assoc,
    successorActionOutput_contraction hπ data j hj a ha]

/-- The whole successor action remains over the original coefficient scheme. -/
@[reassoc] theorem successorGlobalAction_structure :
    successorGlobalAction hπ data j hj a ha ≫ finiteGlobalStructure hπ data (j + 1) hj =
      pullback.fst _ _ ≫ integralSmoothStructure W := by
  calc
    _ = successorGlobalAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj ≫
        finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj) :=
      congrArg (fun t => successorGlobalAction hπ data j hj a ha ≫ t)
        (finiteGlobalStep_structure hπ data j hj).symm
    _ =
      successorActionOutput hπ data j hj a ≫
        finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj) :=
      successorGlobalAction_step_assoc hπ data j hj a ha _
    _ = _ := successorActionOutput_structure hπ data j hj a ha

/-- Every flat scheme restriction of the whole action remains its unique step lift. -/
theorem successorGlobalAction_flat_unique {T : Scheme.{u}}
    (p : T ⟶ finiteGlobalActionProduct hπ data (j + 1) hj) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorGlobalAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorGlobalAction hπ data j hj a ha := by
  apply (show T.OpenCover from (C).pullback₁ p).hom_ext
  intro k
  have he : pullback.snd p ((C).f k) ≫ successorOutputBranchAction hπ data j hj a ha k =
      pullback.fst p ((C).f k) ≫ p ≫ successorGlobalAction hπ data j hj a ha := by
    rw [← successorGlobalAction_branch, ← pullback.condition_assoc]
  change pullback.fst p ((C).f k) ≫ b =
    pullback.fst p ((C).f k) ≫ p ≫ successorGlobalAction hπ data j hj a ha
  rw [← he]
  apply successorOutputBranchAction_flat_unique hπ data j hj a ha k (pullback.snd p ((C).f k))
  simpa only [Category.assoc, hb] using
    congrArg (fun z => z ≫ finiteGlobalStep hπ data j hj) he.symm

end FLT.Mazur.WeierstrassDividedDepth
