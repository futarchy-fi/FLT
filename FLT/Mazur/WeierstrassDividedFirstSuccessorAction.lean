/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstDividedAction
public import FLT.Mazur.WeierstrassDividedFirstExteriorAction
public import FLT.Mazur.WeierstrassDividedFirstInfinityAction
public import FLT.Mazur.WeierstrassDividedFirstOutputCover

/-!
# The action on the entire first finite successor

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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

local notation "C" => firstActionOutputCover hπ data hn

/-- The constructed action on every output branch of the whole successor source. -/
def firstOutputBranchAction (j : Option Bool) :
    (C).X j ⟶ finiteGlobalModel hπ data 1 hn :=
  match j with
  | none => firstInfinityOutputAction hπ data hn
  | some false => firstExteriorOutputAction hπ data hn
  | some true => firstDividedAction hπ data hn

/-- All output branches retain exactly the existing initial-action output. -/
@[reassoc] theorem firstOutputBranchAction_step (j : Option Bool) :
    firstOutputBranchAction hπ data hn j ≫ finiteGlobalStep hπ data 0 hn =
      (C).f j ≫ firstActionOutput hπ data hn := by
  rcases j with _ | (_ | _)
  · exact firstInfinityOutputAction_step hπ data hn
  · exact firstExteriorOutputAction_step hπ data hn
  · exact firstDividedAction_output hπ data hn

/-- Each output branch is uniquely characterized after every flat scheme restriction. -/
theorem firstOutputBranchAction_flat_unique (j : Option Bool) {T : Scheme.{u}}
    (p : T ⟶ (C).X j) [Flat p] (b : T ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstOutputBranchAction hπ data hn j ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstOutputBranchAction hπ data hn j := by
  rcases j with _ | (_ | _)
  · apply firstInfinityOutputAction_unique hπ data hn p b
    simpa only [firstOutputBranchAction, firstInfinityOutputAction_step] using hb
  · apply firstExteriorOutputAction_unique hπ data hn p b
    simpa only [firstOutputBranchAction, firstExteriorOutputAction_step] using hb
  · exact firstDividedAction_flat_unique hπ data hn p b hb

/-- The actual output actions agree on all complete scheme-theoretic intersections. -/
theorem firstOutputBranchAction_overlap (i j : Option Bool) :
    pullback.fst ((C).f i) ((C).f j) ≫ firstOutputBranchAction hπ data hn i =
      pullback.snd ((C).f i) ((C).f j) ≫ firstOutputBranchAction hπ data hn j := by
  symm
  apply firstOutputBranchAction_flat_unique hπ data hn i (pullback.fst ((C).f i) ((C).f j))
  simp only [Category.assoc, firstOutputBranchAction_step]
  rw [pullback.condition_assoc]

/-- The genuine action map on the whole first successor model. -/
irreducible_def firstSuccessorAction : finiteGlobalActionProduct hπ data 1 hn ⟶
    finiteGlobalModel hπ data 1 hn :=
  (C).glueMorphisms (firstOutputBranchAction hπ data hn)
    (firstOutputBranchAction_overlap hπ data hn)

/-- The whole action restricts to each of the constructed output actions. -/
@[reassoc] theorem firstSuccessorAction_branch (j : Option Bool) :
    (C).f j ≫ firstSuccessorAction hπ data hn = firstOutputBranchAction hπ data hn j := by
  rw [firstSuccessorAction_def]
  exact (C).ι_glueMorphisms _ _ j

/-- The whole successor action contracts to precisely the existing initial action. -/
@[reassoc] theorem firstSuccessorAction_step :
    firstSuccessorAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn =
      firstActionOutput hπ data hn := by
  apply (C).hom_ext
  intro j
  rw [firstSuccessorAction_branch_assoc, firstOutputBranchAction_step]

/-- The entire action preserves the actual original input pair and smooth addition. -/
@[reassoc] theorem firstSuccessorAction_original :
    firstSuccessorAction hπ data hn ≫ finiteGlobalContraction hπ data 1 hn =
      finiteGlobalActionInput hπ data 1 hn ≫ leftSmoothFactorAddition W := by
  rw [← finiteGlobalStep_contraction hπ data 0 hn, firstSuccessorAction_step_assoc,
    firstActionOutput_contraction]

/-- The whole successor action remains over the original coefficient scheme. -/
@[reassoc] theorem firstSuccessorAction_structure :
    firstSuccessorAction hπ data hn ≫ finiteGlobalStructure hπ data 1 hn =
      pullback.fst _ _ ≫ integralSmoothStructure W := by
  calc
    _ = firstSuccessorAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn ≫
        finiteGlobalStructure hπ data 0 (Nat.zero_le n) :=
      congrArg (fun t => firstSuccessorAction hπ data hn ≫ t)
        (finiteGlobalStep_structure hπ data 0 hn).symm
    _ = firstActionOutput hπ data hn ≫ finiteGlobalStructure hπ data 0 (Nat.zero_le n) :=
      firstSuccessorAction_step_assoc hπ data hn _
    _ = _ := firstActionOutput_structure hπ data hn

/-- Every flat scheme restriction of the whole action remains its unique step lift. -/
theorem firstSuccessorAction_flat_unique {T : Scheme.{u}}
    (p : T ⟶ finiteGlobalActionProduct hπ data 1 hn) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstSuccessorAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstSuccessorAction hπ data hn := by
  apply (show T.OpenCover from (C).pullback₁ p).hom_ext
  intro j
  have he : pullback.snd p ((C).f j) ≫ firstOutputBranchAction hπ data hn j =
      pullback.fst p ((C).f j) ≫ p ≫ firstSuccessorAction hπ data hn := by
    rw [← firstSuccessorAction_branch, ← pullback.condition_assoc]
  change pullback.fst p ((C).f j) ≫ b =
    pullback.fst p ((C).f j) ≫ p ≫ firstSuccessorAction hπ data hn
  rw [← he]
  apply firstOutputBranchAction_flat_unique hπ data hn j (pullback.snd p ((C).f j))
  simpa only [Category.assoc, hb] using
    congrArg (fun z => z ≫ finiteGlobalStep hπ data 0 hn) he.symm

end FLT.Mazur.WeierstrassDividedDepth
