/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Maps.Basic

/-!
# Descending a complete connected component along a quotient map

A saturated component descends as a connected clopen set. This identifies
its entire component downstairs, without an identity-component hypothesis there.
-/

@[expose] public section
namespace FLT.Mazur.ComponentDescent
open Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {p : X → Y} (hp : IsQuotientMap p) {s : Set Y}

include hp

/-- Closedness and openness both descend along the actual quotient topology. -/
theorem isClopen_of_preimage (hs : IsClopen (p ⁻¹' s)) : IsClopen s :=
  ⟨hp.isCoinducing.isClosed_preimage.mp hs.1,
    hp.isCoinducing.isOpen_preimage.mp hs.2⟩

/-- Connectedness of a saturated inverse image descends by surjectivity. -/
theorem isConnected_of_preimage (hs : IsConnected (p ⁻¹' s)) : IsConnected s := by
  have h := hs.image p hp.continuous.continuousOn
  rwa [Set.image_preimage_eq _ hp.surjective] at h

/-- Every point of the descended clopen connected set has precisely that component. -/
theorem connectedComponent_eq_of_preimage
    (hc : IsClopen (p ⁻¹' s)) (hn : IsConnected (p ⁻¹' s))
    {y : Y} (hy : y ∈ s) : connectedComponent y = s :=
  ((isClopen_of_preimage hp hc).connectedComponent_subset hy).antisymm
    ((isConnected_of_preimage hp hn).subset_connectedComponent hy)

/-- A saturated open component upstairs identifies the component of every original point below. -/
theorem connectedComponent_eq_of_component_preimage
    {x : X} (h : p ⁻¹' s = connectedComponent x) (ho : IsOpen (p ⁻¹' s))
    {y : Y} (hy : y ∈ s) : connectedComponent y = s := by
  apply connectedComponent_eq_of_preimage hp _ _ hy
  · exact ⟨h.symm ▸ isClosed_connectedComponent, ho⟩
  · exact h.symm ▸ isConnected_connectedComponent

end FLT.Mazur.ComponentDescent
