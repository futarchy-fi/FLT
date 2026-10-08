/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFiberNeighborhood

/-!
# A proper local family is controlled by its closed fiber

An open subset of a proper family over a local ring contains the whole
family as soon as it contains the closed fiber. The same criterion detects
an arbitrary open cover, including the case of an empty closed fiber.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.Approximation

variable {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec R) [IsProper f]

/-- An open containing the closed fiber of a proper local family is the whole source. -/
theorem eq_top_of_contains_proper_closedFiber (U : X.Opens)
    (hU : Set.range (f.fiberι (IsLocalRing.closedPoint R)) ⊆ U) : U = ⊤ := by
  obtain ⟨V, hV, hVU⟩ := exists_proper_fiber_neighborhood f (IsLocalRing.closedPoint R) U hU
  have he : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).mp hV
  rw [he, Scheme.Hom.preimage_top] at hVU
  exact top_le_iff.mp hVU

/-- Opens covering the closed fiber cover a proper family over a local ring. -/
theorem iSup_eq_top_of_proper_closedFiber_cover {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ x : f.fiber (IsLocalRing.closedPoint R),
      ∃ i, f.fiberι (IsLocalRing.closedPoint R) x ∈ U i) : (⨆ i, U i) = ⊤ := by
  apply eq_top_of_contains_proper_closedFiber f
  rintro _ ⟨x, rfl⟩
  exact Opens.mem_iSup.mpr (hU x)

end FLT.Mazur.Approximation
