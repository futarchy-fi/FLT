/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedCompleteRelation

/-!
# Exact moving-action equations detected by surjective scheme tests

A permutation equation for an original relation arrow can be detected after any
surjective scheme morphism. In particular a nilpotent closed thickening preserves
the exact equation, rather than only its reduction. The proof uses the open
action graph, not cancellation of the surjective morphism as an epimorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {T T' : Scheme.{0}} (i : T' ⟶ T) [Surjective i]
  (z : T ⟶ fullRelation p q I o) (σ : Equiv.Perm I)

/-- Surjective tests detect factorization through the original open action graph. -/
theorem actionGraph_factor_of_surjective
    (hσ : ((i ≫ z) ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      (i ≫ z) ≫ relationSecond p q I o) :
    ∃ a : T ⟶ source p q I o, a ≫ actionGraph e I o σ = z := by
  let _ := actionGraph_isOpenImmersion e I o σ
  have h := actionGraph_factor e I o (i ≫ z) σ hσ
  have hr : Set.range z ⊆ Set.range (actionGraph e I o σ) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := i.surjective x
    refine ⟨((i ≫ z) ≫ relationFirst p q I o) y, ?_⟩
    exact congrArg (fun f ↦ f y) h
  exact ⟨IsOpenImmersion.lift _ z hr, IsOpenImmersion.lift_fac _ z hr⟩

/-- The moving endpoint equation lifts exactly across every surjective scheme test. -/
theorem action_equation_of_surjective
    (hσ : ((i ≫ z) ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      (i ≫ z) ≫ relationSecond p q I o) :
    (z ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      z ≫ relationSecond p q I o :=
  (factors_actionGraph_iff e I o z σ).mp
    (actionGraph_factor_of_surjective e I o i z σ hσ)

/-- A surjective reduction both preserves and detects the exact permutation equation. -/
theorem action_equation_surjective_iff :
    (((i ≫ z) ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      (i ≫ z) ≫ relationSecond p q I o) ↔
    ((z ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      z ≫ relationSecond p q I o) := by
  refine ⟨action_equation_of_surjective e I o i z σ, ?_⟩
  intro h
  simpa only [Category.assoc] using congrArg (fun f ↦ i ≫ f) h

/-- The original arrow equation, with its coefficient morphisms, lifts without reduction. -/
@[reassoc] theorem action_arrow_of_surjective
    (hσ : ((i ≫ z) ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      (i ≫ z) ≫ relationSecond p q I o) :
    z ≫ relationArrow p q I o = z ≫ relationFirst p q I o ≫ actionArrow I o σ := by
  have h := actionGraph_factor e I o z σ (action_equation_of_surjective e I o i z σ hσ)
  simpa only [Category.assoc, actionGraph_arrow] using
    (congrArg (fun f ↦ f ≫ relationArrow p q I o) h).symm

/-- A complete geometric point determines the exact action on its whole infinitesimal test. -/
theorem complete_surjective_field_test_unique_permutation {K : Type} [Field K]
    (u : Spec (.of K) ⟶ T) [Surjective u]
    (hu : Complete I o ((u ≫ z) ≫ relationFirst p q I o)) :
    ∃! τ : Equiv.Perm I,
      (z ≫ relationFirst p q I o) ≫ (action e I o τ).hom =
        z ≫ relationSecond p q I o := by
  let _ : Nonempty T := ⟨u default⟩
  obtain ⟨τ, hτ, _⟩ := complete_original_arrow_unique_permutation e I o
    ((u ≫ z) ≫ relationFirst p q I o) ((u ≫ z) ≫ relationSecond p q I o)
    ((u ≫ z) ≫ relationArrow p q I o)
    (by simp only [Category.assoc, relationArrow_first])
    (by simp only [Category.assoc, relationArrow_second]) hu
  have h := action_equation_of_surjective e I o u z τ hτ
  exact ⟨τ, h, fun ρ hρ ↦ action_unique e I o _ _ ρ τ hρ h⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
