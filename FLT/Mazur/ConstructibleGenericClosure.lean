/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstructibleDenseInterior
public import Mathlib.Topology.Sober

/-!
# Detecting constructible closure at a generic point

A constructible subset accumulates at a generic point precisely when it
contains that point. This turns generic fiber avoidance into an actual open
neighborhood, without changing the underlying scheme or its nilpotents.
-/

public section
open Topology Set
namespace FLT.Mazur.ConstructibleGenericClosure
variable {X : Type*} [TopologicalSpace X] {η : X}
  (hη : IsGenericPoint η (univ : Set X)) {s : Set X}
include hη

/-- A constructible set cannot accumulate at the generic point without containing it. -/
theorem mem_closure_iff (hs : IsConstructible s) : η ∈ closure s ↔ η ∈ s := by
  refine ⟨fun h ↦ ?_, fun h ↦ subset_closure h⟩
  have hd : Dense s := by
    rw [dense_iff_closure_eq]
    exact univ_subset_iff.mp ((hη.mem_closed_set_iff isClosed_closure).mp h)
  have hi : (interior s).Nonempty := by
    let _ : Nonempty X := ⟨η⟩
    exact (ConstructibleDenseInterior.dense_interior hs hd).nonempty
  exact interior_subset ((hη.mem_open_set_iff isOpen_interior).mpr (by simpa using hi))

/-- Avoiding a constructible set generically gives the canonical open complement of its closure. -/
theorem mem_compl_closure_iff (hs : IsConstructible s) :
    η ∈ (closure s)ᶜ ↔ η ∉ s := not_congr (mem_closure_iff hη hs)

/-- The canonical avoidance neighborhood is nonempty exactly when the generic point avoids it. -/
theorem compl_closure_nonempty_iff (hs : IsConstructible s) :
    ((closure s)ᶜ).Nonempty ↔ η ∉ s := by
  rw [← mem_compl_closure_iff hη hs, hη.mem_open_set_iff isClosed_closure.isOpen_compl]
  simp only [univ_inter]

end FLT.Mazur.ConstructibleGenericClosure
