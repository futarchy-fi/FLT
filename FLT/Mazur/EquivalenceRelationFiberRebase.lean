/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Rebasing the entire fiber of an internal equivalence relation

An original relation arrow identifies the whole first-endpoint fibers over
its two endpoints. The identification preserves the independent second endpoint.
This uses actual pullbacks and does not choose a finite part of the relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.EquivalenceRelationFiber
variable {C : Type*} [Category* C]
  {D A T : C} {p q : D ⟶ A} (e : CategoryTheory.EquivalenceRelation p q)

/-- Compose two original relation arrows on any common test. -/
def compose {U : C} (a b : U ⟶ D) (h : a ≫ q = b ≫ p) : U ⟶ D :=
  e.isLimit.lift (PullbackCone.mk a b h) ≫ e.t

/-- Composition retains the first endpoint of the first arrow. -/
@[reassoc (attr := simp)] theorem compose_fst {U : C} (a b : U ⟶ D) (h) :
    compose e a b h ≫ p = a ≫ p := by
  rw [compose, Category.assoc, e.transitivity₁, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ p) (e.isLimit.fac (PullbackCone.mk a b h) .left)

/-- Composition retains the independent second endpoint of the second arrow. -/
@[reassoc (attr := simp)] theorem compose_snd {U : C} (a b : U ⟶ D) (h) :
    compose e a b h ≫ q = b ≫ q := by
  rw [compose, Category.assoc, e.transitivity₂, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ q) (e.isLimit.fac (PullbackCone.mk a b h) .right)

variable [HasPullbacks C] (a : T ⟶ D)

/-- Rebase every original arrow, with no restriction on its second endpoint. -/
def rebaseArrow : pullback p (a ≫ p) ⟶ D :=
  compose e (pullback.snd p (a ≫ p) ≫ a ≫ e.s) (pullback.fst p (a ≫ p)) (by
    simp only [Category.assoc, e.symmetry₂, pullback.condition])

/-- The new first endpoint is the other endpoint of the given original arrow. -/
@[reassoc (attr := simp)] theorem rebaseArrow_fst :
    rebaseArrow e a ≫ p = pullback.snd p (a ≫ p) ≫ a ≫ q := by
  rw [rebaseArrow, compose_fst, Category.assoc, Category.assoc, e.symmetry₁]

/-- Rebasing keeps the original second endpoint unchanged. -/
@[reassoc (attr := simp)] theorem rebaseArrow_snd :
    rebaseArrow e a ≫ q = pullback.fst p (a ≫ p) ≫ q := compose_snd e _ _ _

/-- The actual map between the entire original fibers. -/
def rebase : pullback p (a ≫ p) ⟶ pullback p (a ≫ q) :=
  pullback.lift (rebaseArrow e a) (pullback.snd p (a ≫ p)) (rebaseArrow_fst e a)

/-- The first projection is the constructed original rebased arrow. -/
@[reassoc (attr := simp)] theorem rebase_fst :
    rebase e a ≫ pullback.fst p (a ≫ q) = rebaseArrow e a := pullback.lift_fst _ _ _

/-- The test and hence its coefficient morphism are unchanged. -/
@[reassoc (attr := simp)] theorem rebase_snd :
    rebase e a ≫ pullback.snd p (a ≫ q) = pullback.snd p (a ≫ p) :=
  pullback.lift_snd _ _ _

/-- Rebase back using the forward original arrow. -/
def unrebaseArrow : pullback p (a ≫ q) ⟶ D :=
  compose e (pullback.snd p (a ≫ q) ≫ a) (pullback.fst p (a ≫ q)) (by
    rw [Category.assoc, pullback.condition])

/-- Reverse rebasing restores the original first endpoint. -/
@[reassoc (attr := simp)] theorem unrebaseArrow_fst :
    unrebaseArrow e a ≫ p = pullback.snd p (a ≫ q) ≫ a ≫ p := by
  rw [unrebaseArrow, compose_fst, Category.assoc]

/-- Reverse rebasing also preserves the independent second endpoint. -/
@[reassoc (attr := simp)] theorem unrebaseArrow_snd :
    unrebaseArrow e a ≫ q = pullback.fst p (a ≫ q) ≫ q := compose_snd e _ _ _

/-- The inverse map on the full original pullbacks. -/
def unrebase : pullback p (a ≫ q) ⟶ pullback p (a ≫ p) :=
  pullback.lift (unrebaseArrow e a) (pullback.snd p (a ≫ q)) (unrebaseArrow_fst e a)

/-- Reverse rebasing is the original reverse arrow after projection. -/
@[reassoc (attr := simp)] theorem unrebase_fst :
    unrebase e a ≫ pullback.fst p (a ≫ p) = unrebaseArrow e a :=
  pullback.lift_fst _ _ _

/-- Reverse rebasing retains the same test. -/
@[reassoc (attr := simp)] theorem unrebase_snd :
    unrebase e a ≫ pullback.snd p (a ≫ p) = pullback.snd p (a ≫ q) :=
  pullback.lift_snd _ _ _

/-- The whole original fibers are isomorphic over the test, including their structure. -/
def rebaseIso : pullback p (a ≫ p) ≅ pullback p (a ≫ q) where
  hom := rebase e a
  inv := unrebase e a
  hom_inv_id := by
    apply pullback.hom_ext
    · apply e.right_cancellation
      · simp only [Category.assoc, unrebase_fst, unrebaseArrow_fst, rebase_snd_assoc,
          Category.id_comp, pullback.condition]
      · simp only [Category.assoc, unrebase_fst, unrebaseArrow_snd, rebase_fst_assoc,
          rebaseArrow_snd, Category.id_comp]
    · simp only [Category.assoc, unrebase_snd, rebase_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply e.right_cancellation
      · simp only [Category.assoc, rebase_fst, rebaseArrow_fst, unrebase_snd_assoc,
          Category.id_comp, pullback.condition]
      · simp only [Category.assoc, rebase_fst, rebaseArrow_snd, unrebase_fst_assoc,
          unrebaseArrow_snd, Category.id_comp]
    · simp only [Category.assoc, rebase_snd, unrebase_snd, Category.id_comp]

end FLT.Mazur.EquivalenceRelationFiber
