/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameAction

/-!
# Freeness and coefficient compatibility of normalized frame permutations

The rebasing action is free on every nonempty scheme test. Every coefficient
morphism equalized by the original relation is invariant under this action.
The original transition arrows satisfy the identity and composition laws.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

local instance freeOverFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local notation "N" => source p q I o

include e in
/-- Every independent second endpoint remains distinct on every nonempty test. -/
theorem second_injective {T : Scheme} [Nonempty T] (a : T ⟶ N) :
    Function.Injective (fun i ↦ a ≫ coordinate p q I o i ≫ q) := by
  intro i j h
  apply distinctCoordinate_left_injective (Over.mk p) I (a ≫ inclusion p q I o)
  change a ≫ coordinate p q I o i = a ≫ coordinate p q I o j
  apply e.right_cancellation
  · rw [Category.assoc, coordinate_first, Category.assoc, coordinate_first]
  · simpa only [Category.assoc] using h

/-- The endpoint-moving action is free on any nonempty scheme test. -/
theorem action_free {T : Scheme} [Nonempty T] (a : T ⟶ N) (σ : Equiv.Perm I)
    (h : a ≫ (action e I o σ).hom = a) : σ = 1 := by
  apply Equiv.ext
  intro i
  have hs := congrArg (fun z ↦ z ≫ coordinate p q I o (σ i) ≫ q) h
  change (a ≫ actionMap e I o σ) ≫ coordinate p q I o (σ i) ≫ q = _ at hs
  rw [Category.assoc, actionMap_second, σ.symm_apply_apply] at hs
  exact (second_injective e I o a hs).symm

/-- There is at most one normalized permutation matching two nonempty tests. -/
theorem action_unique {T : Scheme} [Nonempty T] (a b : T ⟶ N)
    (σ τ : Equiv.Perm I) (hσ : a ≫ (action e I o σ).hom = b)
    (hτ : a ≫ (action e I o τ).hom = b) : σ = τ := by
  have hs : σ.symm = τ.symm := by
    apply Equiv.ext
    intro i
    apply second_injective e I o a
    have h := congrArg (fun z ↦ z ≫ coordinate p q I o i ≫ q) (hσ.trans hτ.symm)
    change (a ≫ actionMap e I o σ) ≫ coordinate p q I o i ≫ q =
      (a ≫ actionMap e I o τ) ≫ coordinate p q I o i ≫ q at h
    simpa only [Category.assoc, actionMap_second] using h
  exact congrArg Equiv.symm hs

/-- Every original equalized coefficient map is preserved by the moving-endpoint action. -/
@[reassoc] theorem action_coefficients {S : Scheme} (c : A ⟶ S) (hc : p ≫ c = q ≫ c)
    (σ : Equiv.Perm I) :
    (action e I o σ).hom ≫ first p q I o ≫ c = first p q I o ≫ c := by
  change actionMap e I o σ ≫ first p q I o ≫ c = _
  rw [← Category.assoc, actionMap_first, Category.assoc, ← hc,
    ← Category.assoc, coordinate_first]

/-- The identity transition is the original reflexive relation arrow. -/
theorem actionArrow_one :
    actionArrow (p := p) (q := q) I o 1 = first p q I o ≫ e.r :=
  distinguished_eq_identity p q I o e

/-- Successive transition arrows have the required common original endpoint. -/
theorem actionArrow_composable (σ τ : Equiv.Perm I) :
    actionArrow (p := p) (q := q) I o τ ≫ q =
      (action e I o τ).hom ≫ actionArrow (p := p) (q := q) I o σ ≫ p := by
  rw [actionArrow_first, actionArrow_second e]

/-- The transition for a product is the composite of the actual original relation arrows. -/
theorem actionArrow_mul (σ τ : Equiv.Perm I) :
    actionArrow (p := p) (q := q) I o (σ * τ) = compose e
      (actionArrow (p := p) (q := q) I o τ)
      ((action e I o τ).hom ≫ actionArrow (p := p) (q := q) I o σ)
      (by simpa only [Category.assoc] using actionArrow_composable e I o σ τ) := by
  apply e.right_cancellation
  · rw [actionArrow_first, compose_fst, actionArrow_first]
  · rw [compose_snd, actionArrow_second e, Category.assoc, actionArrow_second e]
    change actionMap e I o (σ * τ) ≫ first p q I o =
      actionMap e I o τ ≫ actionMap e I o σ ≫ first p q I o
    simpa only [Category.assoc] using
      congrArg (fun z ↦ z ≫ first p q I o) (actionMap_mul e I o σ τ)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
