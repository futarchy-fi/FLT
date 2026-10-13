/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.GDelta.Basic

/-!
# Dense open interiors of constructible images

A constructible set has nowhere dense frontier. Consequently a dense
constructible image contains a canonical dense open, with no irreducibility
or reducedness assumption on the target.
-/

public section
open Topology Set
namespace FLT.Mazur.ConstructibleDenseInterior
variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- Finite Boolean combinations of open sets have nowhere dense frontier. -/
theorem frontier_isNowhereDense (hs : IsConstructible s) : IsNowhereDense (frontier s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    apply isClosed_frontier.isNowhereDense_iff.mpr
    rw [← frontier_compl]
    exact interior_frontier hU.isClosed_compl
  | union s _ t _ hs ht =>
    exact (hs.union ht).mono ((frontier_union_subset s t).trans
      (union_subset_union inter_subset_left inter_subset_right))
  | compl s _ hs =>
    rwa [frontier_compl]

/-- The interior of a dense constructible set is itself dense. -/
theorem dense_interior (hs : IsConstructible s) (hd : Dense s) : Dense (interior s) := by
  have hf : interior (frontier s) = ∅ :=
    isClosed_frontier.isNowhereDense_iff.mp (frontier_isNowhereDense hs)
  have he : frontier s = (interior s)ᶜ := by
    rw [frontier, hd.closure_eq, ← compl_eq_univ_sdiff]
  rw [he] at hf
  simpa only [compl_compl] using interior_eq_empty_iff_dense_compl.mp hf

/-- The canonical dense open never introduces points outside the original image. -/
theorem exists_dense_open_subset (hs : IsConstructible s) (hd : Dense s) :
    ∃ U : TopologicalSpace.Opens X, Dense (U : Set X) ∧ (U : Set X) ⊆ s :=
  ⟨⟨interior s, isOpen_interior⟩, dense_interior hs hd, interior_subset⟩

end FLT.Mazur.ConstructibleDenseInterior
