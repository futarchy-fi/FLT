/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.Irreducible

/-!
# OpenIrreducibleComponent

The closure of a nonempty irreducible open subset is an irreducible component.
-/

@[expose] public noncomputable section

open Set TopologicalSpace
namespace FLT.Mazur.OpenIrreducibleComponent
variable {X : Type*} [TopologicalSpace X] {U : Set X}
theorem closure_mem (ho : IsOpen U) (hi : IsIrreducible U) :
    closure U ∈ irreducibleComponents X := by
  refine ⟨hi.closure, ?_⟩
  intro V hV hUV
  have hn : (V ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hi.nonempty
    exact ⟨x, hUV (subset_closure hx), hx⟩
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen hV.2 ho hn).trans
    (closure_mono inter_subset_right)
end FLT.Mazur.OpenIrreducibleComponent
