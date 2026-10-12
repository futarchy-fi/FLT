/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension

/-!
# Positive dimensional connected Jacobson spaces have no discrete open charts

An isolated point in a Jacobson space is closed. Connectedness would then
force the whole space to be that point, contradicting positive dimension.
-/

@[expose] public noncomputable section
open TopologicalSpace
namespace FLT.Mazur.FCurve

/-- A positive dimensional connected Jacobson space cannot contain an isolated point. -/
theorem not_isOpen_singleton_of_positive_dimension {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [JacobsonSpace X] (hX : 0 < topologicalKrullDim X) (x : X) :
    ¬ IsOpen ({x} : Set X) := by
  intro ho
  have hc : IsClosed ({x} : Set X) :=
    isClosed_singleton_of_isLocallyClosed_singleton ho.isLocallyClosed
  have he : ({x} : Set X) = Set.univ := (show IsClopen ({x} : Set X) from ⟨hc, ho⟩).eq_univ ⟨x, rfl⟩
  have hs : Subsingleton X := ⟨fun a b ↦ by
    have ha : a = x := Set.mem_singleton_iff.mp (he.symm ▸ Set.mem_univ a)
    have hb : b = x := Set.mem_singleton_iff.mp (he.symm ▸ Set.mem_univ b)
    exact ha.trans hb.symm⟩
  let _ := hs
  exact (not_le_of_gt hX) (topologicalKrullDim_zero_of_discreteTopology X)

/-- A nonempty discrete space cannot embed openly in such a space. -/
theorem not_openEmbedding_discrete_of_positive_dimension
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace X] [JacobsonSpace X] [DiscreteTopology Y] [Nonempty Y]
    (hX : 0 < topologicalKrullDim X) (f : Y → X) : ¬ Topology.IsOpenEmbedding f := by
  intro hf
  obtain ⟨y⟩ := ‹Nonempty Y›
  apply not_isOpen_singleton_of_positive_dimension hX (f y)
  simpa only [Set.image_singleton] using hf.isOpenMap {y} (isOpen_discrete _)

end FLT.Mazur.FCurve
