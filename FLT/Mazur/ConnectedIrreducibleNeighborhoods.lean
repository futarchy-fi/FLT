/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sets.Opens

/-!
# Connected spaces with irreducible open neighborhoods

An irreducible open meeting an irreducible component lies entirely in that
component. Such neighborhoods make every component open as well as closed;
connectedness forces the component to be the whole space.
-/

@[expose] public noncomputable section
open TopologicalSpace Set
namespace FLT.Mazur.FCurve

variable {X : Type*} [TopologicalSpace X]

/-- Irreducible open neighborhoods make each irreducible component open. -/
theorem isOpen_component_of_irreducible_neighborhoods
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IrreducibleSpace U)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U, hxU, hU⟩ := h x
  let _ := hU
  have hp := preimage_mem_irreducibleComponents hZ U.isOpenEmbedding'
    ⟨x, hx, ⟨⟨x, hxU⟩, rfl⟩⟩
  have he : (Subtype.val : U → X) ⁻¹' Z = univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hp
  apply Filter.mem_of_superset (U.isOpen.mem_nhds hxU)
  intro y hy
  have : (⟨y, hy⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' Z := he ▸ Set.mem_univ _
  exact this

/-- A connected space covered locally by irreducible opens is irreducible. -/
theorem irreducibleSpace_of_connected_of_irreducible_neighborhoods [ConnectedSpace X]
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IrreducibleSpace U) : IrreducibleSpace X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have ho := isOpen_component_of_irreducible_neighborhoods h (irreducibleComponent x)
    (irreducibleComponent_mem_irreducibleComponents x)
  have he := IsClopen.eq_univ ⟨isClosed_irreducibleComponent, ho⟩
    (show (irreducibleComponent x).Nonempty from ⟨x, mem_irreducibleComponent⟩)
  exact { toNonempty := inferInstance, isPreirreducible_univ := he ▸
    (isIrreducible_irreducibleComponent (x := x)).isPreirreducible }

end FLT.Mazur.FCurve
