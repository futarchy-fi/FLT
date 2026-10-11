/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorFractionGluing
public import FLT.Mazur.WeierstrassDividedSuccessorInfinityInputAction
public import FLT.Mazur.WeierstrassDividedSuccessorRetainedGluing

/-!
# The action on the entire successor divided-output domain

All five input branches now carry constructed actions. Their exact step
contractions and proved uniqueness identify every full intersection, so
they glue to an action on the entire divided-output domain.
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
  (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))
  (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
    finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
local notation "v" => finiteNormalizedChart hπ data j hj
local notation "D" => successorDividedInputCover hπ data j hj a

/-- Every input branch of the entire divided-output domain has an actual successor action. -/
def successorDividedBranchAction (k : Option (Option (Fin 3))) :
    (D).X k ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  match k with
  | none => successorInfinityInputAction hπ data j hj a ha
  | some none => successorRetainedAction hπ data j hj a ha
  | some (some i) => successorFractionInputAction hπ data j hj a ha i

/-- Every branch retains the same actual divided output. -/
@[reassoc] theorem successorDividedBranchAction_step (k : Option (Option (Fin 3))) :
    successorDividedBranchAction hπ data j hj a ha k ≫ finiteGlobalStep hπ data j hj =
      (D).f k ≫ pullback.snd _ _ ≫ v := by
  rcases k with _ | (_ | i)
  · exact successorInfinityInputAction_step hπ data j hj a ha
  · exact successorRetainedAction_step hπ data j hj a ha
  · exact successorFractionInputAction_step hπ data j hj a ha i

/-- Branch lifts are uniquely determined after any flat scheme restriction. -/
theorem successorDividedBranchAction_flat_unique (k : Option (Option (Fin 3)))
    {T : Scheme.{u}} (p : T ⟶ (D).X k) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorDividedBranchAction hπ data j hj a ha k ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorDividedBranchAction hπ data j hj a ha k := by
  rcases k with _ | (_ | i)
  · exact successorInfinityInputAction_unique hπ data j hj a ha p b hb
  · exact successorRetainedAction_unique hπ data j hj a ha p b hb
  · exact successorFractionInputAction_flat_unique hπ data j hj a ha i p b hb

/-- All five actual branch actions agree on their full scheme-theoretic intersections. -/
theorem successorDividedBranchAction_overlap (i k : Option (Option (Fin 3))) :
    pullback.fst ((D).f i) ((D).f k) ≫ successorDividedBranchAction hπ data j hj a ha i =
      pullback.snd ((D).f i) ((D).f k) ≫ successorDividedBranchAction hπ data j hj a ha k := by
  symm
  apply successorDividedBranchAction_flat_unique hπ data j hj a ha i
    (pullback.fst ((D).f i) ((D).f k))
  simp only [Category.assoc, successorDividedBranchAction_step]
  rw [pullback.condition_assoc]

/-- The actual action on every successor input whose output is divided. -/
irreducible_def successorDividedAction : successorDividedOutputDomain hπ data j hj a ⟶
    finiteGlobalModel hπ data (j + 1) hj :=
  (D).glueMorphisms (successorDividedBranchAction hπ data j hj a ha)
    (successorDividedBranchAction_overlap hπ data j hj a ha)

/-- The glued action recovers every fraction and crossed branch action. -/
@[reassoc] theorem successorDividedAction_branch (k : Option (Option (Fin 3))) :
    (D).f k ≫ successorDividedAction hπ data j hj a ha =
      successorDividedBranchAction hπ data j hj a ha k := by
  rw [successorDividedAction_def]
  exact (D).ι_glueMorphisms _ _ k

/-- The full divided-domain action retains exactly the prescribed normalized output. -/
@[reassoc] theorem successorDividedAction_step :
    successorDividedAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj =
      pullback.snd _ _ ≫ v := by
  apply (D).hom_ext
  intro k
  rw [successorDividedAction_branch_assoc, successorDividedBranchAction_step]

/-- The divided-domain action has the original preceding-action output. -/
@[reassoc] theorem successorDividedAction_output :
    successorDividedAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj =
      pullback.fst _ _ ≫ successorActionOutput hπ data j hj a := by
  rw [successorDividedAction_step, pullback.condition]

/-- The entire divided-domain action stays unique after arbitrary flat scheme restriction. -/
theorem successorDividedAction_flat_unique {T : Scheme.{u}}
    (p : T ⟶ successorDividedOutputDomain hπ data j hj a) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorDividedAction hπ data j hj a ha ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorDividedAction hπ data j hj a ha := by
  apply (show T.OpenCover from (D).pullback₁ p).hom_ext
  intro k
  have he : pullback.snd p ((D).f k) ≫ successorDividedBranchAction hπ data j hj a ha k =
      pullback.fst p ((D).f k) ≫ p ≫ successorDividedAction hπ data j hj a ha := by
    rw [← successorDividedAction_branch, ← pullback.condition_assoc]
  change pullback.fst p ((D).f k) ≫ b =
    pullback.fst p ((D).f k) ≫ p ≫ successorDividedAction hπ data j hj a ha
  rw [← he]
  apply successorDividedBranchAction_flat_unique hπ data j hj a ha k (pullback.snd p ((D).f k))
  simpa only [Category.assoc, hb] using
    congrArg (fun z => z ≫ finiteGlobalStep hπ data j hj) he.symm

end FLT.Mazur.WeierstrassDividedDepth
