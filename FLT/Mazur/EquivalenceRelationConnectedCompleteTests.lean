/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSourceComparison
public import Mathlib.Topology.Connected.Clopen

/-!
# A single exact permutation on a connected complete test

On a connected scheme test supported on complete frames, the locally varying
permutation is one unique permutation. Both endpoint equations and the original
arrow equation hold as scheme morphisms, without reducing the test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Connected scheme maps to a coproduct factor through an actual component. -/
theorem connected_coproduct_factor {J : Type} (X : J → Scheme.{0})
    {T : Scheme.{0}} [ConnectedSpace T] (w : T ⟶ ∐ X) :
    ∃ (j : J) (a : T ⟶ X j), a ≫ Sigma.ι X j = w := by
  let f : T → Σ j, X j := fun x ↦ (sigmaMk X).symm (w x)
  have hf : Continuous f := (sigmaMk X).symm.continuous.comp w.continuous
  obtain ⟨j, g, _, hg⟩ := hf.exists_lift_sigma
  have hr : Set.range w ⊆ Set.range (Sigma.ι X j) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨g x, ?_⟩
    have hx := congrArg (sigmaMk X) (congrFun hg x)
    simpa only [f, Function.comp_apply, Homeomorph.apply_symm_apply, sigmaMk_mk] using hx.symm
  exact ⟨j, IsOpenImmersion.lift _ w hr, IsOpenImmersion.lift_fac _ w hr⟩

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {T : Scheme.{0}} [ConnectedSpace T] (z : T ⟶ fullRelation p q I o)
  (hz : Set.range (z ≫ relationFirst p q I o) ⊆
    completePointLocus (p := p) (q := q) I o)

include hz in
/-- A connected complete test lies in one original permutation graph as a scheme. -/
theorem connected_complete_graph :
    ∃ σ : Equiv.Perm I, ∃ a : T ⟶ source p q I o, a ≫ actionGraph e I o σ = z := by
  obtain ⟨σ, a, ha⟩ := connected_coproduct_factor _ (completeSourceLift e I o z hz)
  refine ⟨σ, a, ?_⟩
  rw [← component_relationComparison e I o σ, ← Category.assoc, ha,
    completeSourceLift_comparison]

include hz in
/-- The moving endpoint is one unique exact permutation on the entire connected test. -/
theorem connected_complete_unique_permutation :
    ∃! σ : Equiv.Perm I,
      (z ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
        z ≫ relationSecond p q I o := by
  obtain ⟨σ, a, ha⟩ := connected_complete_graph e I o z hz
  have hσ := (factors_actionGraph_iff e I o z σ).mp ⟨a, ha⟩
  exact ⟨σ, hσ, fun τ hτ ↦ action_unique e I o _ _ τ σ hτ hσ⟩

omit [Etale p] [ConnectedSpace T] in
/-- The exact endpoint equation also determines the original arrow and coefficient map. -/
@[reassoc] theorem connected_permutation_arrow (σ : Equiv.Perm I)
    (hσ : (z ≫ relationFirst p q I o) ≫ (action e I o σ).hom =
      z ≫ relationSecond p q I o) :
    z ≫ relationArrow p q I o =
      z ≫ relationFirst p q I o ≫ actionArrow I o σ := by
  have h := congrArg (fun f ↦ f ≫ relationArrow p q I o) (actionGraph_factor e I o z σ hσ)
  simpa only [Category.assoc, actionGraph_arrow] using h.symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames
