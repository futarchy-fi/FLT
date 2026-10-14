/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedSubsets

/-!
# Finite complements in a surjective image of an integral curve

Pull a nonempty target open back to the source curve. Its complement is a
proper closed subset and hence finite; surjectivity covers the target complement.
No dimension formula for the target or normality assumption is required.
-/

@[expose] public section
open TopologicalSpace
namespace FLT.Mazur.FCurve

/-- A nonempty open in a surjective continuous image of a Noetherian curve has finite complement. -/
theorem finite_compl_open_of_curve_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [T0Space X] [IrreducibleSpace X]
    (hd : topologicalKrullDim X ≤ 1) (f : X → Y) (hf : Continuous f)
    (hs : Function.Surjective f) (U : Opens Y) (hU : (U : Set Y).Nonempty) :
    (U : Set Y)ᶜ.Finite := by
  have hc : (f ⁻¹' (U : Set Y)ᶜ).Finite := by
    apply finite_of_isClosed_of_ne_univ hd (U.isOpen.isClosed_compl.preimage hf)
    intro he
    obtain ⟨y, hy⟩ := hU
    obtain ⟨x, rfl⟩ := hs y
    have hx : x ∈ f ⁻¹' (U : Set Y)ᶜ := he.symm ▸ Set.mem_univ x
    exact hx hy
  apply (hc.image f).subset
  intro y hy
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨x, hy, rfl⟩

end FLT.Mazur.FCurve
