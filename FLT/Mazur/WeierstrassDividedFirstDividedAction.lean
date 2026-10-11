/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstAtlasFractionAction
public import FLT.Mazur.WeierstrassDividedFirstCrossedAction

/-!
# The action on the entire first-successor divided-output domain

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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => previousOriginalMap hπ d e
local notation "g" => WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "hg" => WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "D" => firstDividedInputCover hπ data hn

/-- The transported fraction action stays unique on every flat scheme restriction. -/
theorem firstDividedFractionAction_flat_unique (i : Fin 3) {T : Scheme.{u}}
    (p : T ⟶ (D).X (some (some i))) [Flat p] (b : T ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstDividedFractionAction hπ data hn i ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstDividedFractionAction hπ data hn i := by
  rw [firstDividedFractionAction, ← Category.assoc]
  apply firstFractionDomainAction_flat_unique hπ data hn (g i) (hg i)
    (p ≫ (firstFractionDomainIso hπ data hn (g i) (hg i)).inv)
  simpa only [firstDividedFractionAction, Category.assoc] using hb

/-- Every input branch of the entire divided-output domain has an actual successor action. -/
def firstDividedBranchAction (j : Option (Option (Fin 3))) :
    (D).X j ⟶ finiteGlobalModel hπ data 1 hn :=
  match j with
  | none => firstDividedCrossedAction hπ data hn none (Or.inl rfl)
  | some none => firstDividedCrossedAction hπ data hn (some none) (Or.inr rfl)
  | some (some i) => firstDividedFractionAction hπ data hn i

/-- Every branch retains the same actual divided output. -/
@[reassoc] theorem firstDividedBranchAction_step (j : Option (Option (Fin 3))) :
    firstDividedBranchAction hπ data hn j ≫ finiteGlobalStep hπ data 0 hn =
      (D).f j ≫ pullback.snd _ _ ≫ v := by
  rcases j with _ | (_ | i)
  · exact firstDividedCrossedAction_step hπ data hn none (Or.inl rfl)
  · exact firstDividedCrossedAction_step hπ data hn (some none) (Or.inr rfl)
  · exact firstDividedFractionAction_step hπ data hn i

/-- Branch lifts are uniquely determined after any flat scheme restriction. -/
theorem firstDividedBranchAction_flat_unique (j : Option (Option (Fin 3)))
    {T : Scheme.{u}} (p : T ⟶ (D).X j) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstDividedBranchAction hπ data hn j ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstDividedBranchAction hπ data hn j := by
  rcases j with _ | (_ | i)
  · exact firstDividedCrossedAction_unique hπ data hn none (Or.inl rfl) p b hb
  · exact firstDividedCrossedAction_unique hπ data hn (some none) (Or.inr rfl) p b hb
  · exact firstDividedFractionAction_flat_unique hπ data hn i p b hb

/-- All five actual branch actions agree on their full scheme-theoretic intersections. -/
theorem firstDividedBranchAction_overlap (i j : Option (Option (Fin 3))) :
    pullback.fst ((D).f i) ((D).f j) ≫ firstDividedBranchAction hπ data hn i =
      pullback.snd ((D).f i) ((D).f j) ≫ firstDividedBranchAction hπ data hn j := by
  symm
  apply firstDividedBranchAction_flat_unique hπ data hn i (pullback.fst ((D).f i) ((D).f j))
  simp only [Category.assoc, firstDividedBranchAction_step]
  rw [pullback.condition_assoc]

/-- The actual action on every first-successor input whose output is divided. -/
irreducible_def firstDividedAction : firstDividedOutputDomain hπ data hn ⟶
    finiteGlobalModel hπ data 1 hn :=
  (D).glueMorphisms (firstDividedBranchAction hπ data hn)
    (firstDividedBranchAction_overlap hπ data hn)

/-- The glued action recovers every fraction and crossed branch action. -/
@[reassoc] theorem firstDividedAction_branch (j : Option (Option (Fin 3))) :
    (D).f j ≫ firstDividedAction hπ data hn = firstDividedBranchAction hπ data hn j := by
  rw [firstDividedAction_def]
  exact (D).ι_glueMorphisms _ _ j

/-- The full divided-domain action retains exactly the prescribed normalized output. -/
@[reassoc] theorem firstDividedAction_step :
    firstDividedAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn =
      pullback.snd _ _ ≫ v := by
  apply (D).hom_ext
  intro j
  rw [firstDividedAction_branch_assoc, firstDividedBranchAction_step]

/-- The divided-domain action has the original initial-action output. -/
@[reassoc] theorem firstDividedAction_output :
    firstDividedAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn =
      pullback.fst _ _ ≫ firstActionOutput hπ data hn := by
  rw [firstDividedAction_step, pullback.condition]

/-- The entire divided-domain action stays unique after arbitrary flat scheme restriction. -/
theorem firstDividedAction_flat_unique {T : Scheme.{u}}
    (p : T ⟶ firstDividedOutputDomain hπ data hn) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data 1 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstDividedAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn) :
    b = p ≫ firstDividedAction hπ data hn := by
  apply (show T.OpenCover from (D).pullback₁ p).hom_ext
  intro j
  have he : pullback.snd p ((D).f j) ≫ firstDividedBranchAction hπ data hn j =
      pullback.fst p ((D).f j) ≫ p ≫ firstDividedAction hπ data hn := by
    rw [← firstDividedAction_branch, ← pullback.condition_assoc]
  change pullback.fst p ((D).f j) ≫ b =
    pullback.fst p ((D).f j) ≫ p ≫ firstDividedAction hπ data hn
  rw [← he]
  apply firstDividedBranchAction_flat_unique hπ data hn j (pullback.snd p ((D).f j))
  simpa only [Category.assoc, hb] using
    congrArg (fun z => z ≫ finiteGlobalStep hπ data 0 hn) he.symm

end FLT.Mazur.WeierstrassDividedDepth
