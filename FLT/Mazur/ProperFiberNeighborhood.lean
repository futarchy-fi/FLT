/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Shrinking a proper family around a fiber

An open subset containing a fiber contains the inverse image of an open
neighborhood of the base point. In particular, opens where lifted sections
generate can be made to cover after shrinking the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace FLT.Mazur.Approximation

/-- The complement of the closed image of the unwanted locus is the required
base neighborhood. This also handles empty fibers. -/
theorem exists_proper_fiber_neighborhood {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (s : S) (U : X.Opens) (hU : Set.range (f.fiberι s) ⊆ U) :
    ∃ V : S.Opens, s ∈ V ∧ f ⁻¹ᵁ V ≤ U := by
  let V : S.Opens := ⟨(f '' (U : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · change s ∉ f '' (U : Set X)ᶜ
    rintro ⟨x, hx, hxs⟩
    apply hx
    apply hU
    rw [Scheme.Hom.range_fiberι]
    exact hxs
  · intro x hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩

/-- A family of opens covering the chosen fiber covers the family over some
open base neighborhood. No extension of sections is assumed or supplied. -/
theorem exists_proper_fiber_cover_neighborhood {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (s : S) {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ x : f.fiber s, ∃ i, f.fiberι s x ∈ U i) :
    ∃ V : S.Opens, s ∈ V ∧ f ⁻¹ᵁ V ≤ ⨆ i, U i := by
  apply exists_proper_fiber_neighborhood f s
  rintro _ ⟨x, rfl⟩
  exact Opens.mem_iSup.mpr (hU x)

end FLT.Mazur.Approximation
