/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowSimultaneousLineBundle
public import FLT.Mazur.RelativeSerreVanishing

/-!
# Simultaneous Serre vanishing for the Chow line bundle

The two geometric presentations of the same line bundle give two Serre bounds.
Their maximum works for both morphisms and all positive higher direct images.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- All sufficiently large powers of the common Chow line are acyclic for both maps. -/
theorem graphLineBundlePower_eventually_simultaneously_acyclic :
    ∃ N : ℕ, ∀ n ≥ N,
      ModulePushforwardAcyclic (graphClosureπ f) (graphLineBundlePower f n) ∧
      ModulePushforwardAcyclic (graphClosureπ f ≫ f) (graphLineBundlePower f n) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨N, hN⟩ := relativeVeryAmple_eventually_acyclic (graphClosureπ f)
    (graphLineBundle f) (graphLineBundle_relativeVeryAmple f)
  obtain ⟨M, hM⟩ := relativeVeryAmple_eventually_acyclic (graphClosureπ f ≫ f)
    (graphLineBundle f) (graphLineBundle_absoluteVeryAmple f)
  exact ⟨max N M, fun n hn ↦
    ⟨hN n (le_trans (le_max_left _ _) hn), hM n (le_trans (le_max_right _ _) hn)⟩⟩

/-- In particular one actual natural tensor power is acyclic for both maps. -/
theorem exists_graphLineBundlePower_simultaneously_acyclic :
    ∃ n : ℕ,
      ModulePushforwardAcyclic (graphClosureπ f) (graphLineBundlePower f n) ∧
      ModulePushforwardAcyclic (graphClosureπ f ≫ f) (graphLineBundlePower f n) := by
  obtain ⟨N, hN⟩ := graphLineBundlePower_eventually_simultaneously_acyclic f
  exact ⟨N, hN N le_rfl⟩

end FLT.Mazur.Chow
