/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedCompleteRelation

/-!
# Every endpoint from a complete frame occurs in its moving orbit

An arbitrary original arrow starting at a complete geometric frame is one of
its actual coordinates. Moving that coordinate to the distinguished position
constructs a normalized orbit point over the arrow's other endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
local instance endpointOrbitOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance endpointOrbitOver_etale : Etale (Over.mk p).hom := ‹Etale p›
variable {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)
  (hu : Complete I o u) (a : Spec (.of K) ⟶ D)
  (ha : a ≫ p = u ≫ first p q I o)

include hu ha in
/-- Completeness enumerates every actual original arrow with this first endpoint. -/
theorem complete_arrow_coordinate : ∃ i : I, u ≫ coordinate p q I o i = a := by
  let r : Over.mk (u ≫ first p q I o) ⟶ Over.mk p := Over.homMk a ha
  obtain ⟨i, hi⟩ := complete_coordinate_surjective (Over.mk p) I (testFrame I o u) hu r
  refine ⟨i, ?_⟩
  exact congrArg Over.Hom.left hi

include hu ha in
/-- An actual moving permutation reaches the other endpoint of every original arrow. -/
theorem complete_arrow_endpoint_permutation :
    ∃ σ : Equiv.Perm I, u ≫ (action e I o σ).hom ≫ first p q I o = a ≫ q := by
  classical
  obtain ⟨i, hi⟩ := complete_arrow_coordinate I o u hu a ha
  refine ⟨Equiv.swap o i, ?_⟩
  change u ≫ actionMap e I o (Equiv.swap o i) ≫ first p q I o = a ≫ q
  rw [actionMap_first, Equiv.symm_swap, Equiv.swap_apply_left, ← Category.assoc, hi]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
