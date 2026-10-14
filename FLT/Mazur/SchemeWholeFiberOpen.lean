/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The largest target open retaining only whole good fibers

Remove the closure of the image of the bad locus. This gives an actual open
of the unchanged target; its entire inverse image lies in the prescribed
source open. No properness or closed-image assertion is used, and the open
may be empty. In particular the construction retains nilpotent structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeWholeFiberOpen
variable {K T : Scheme.{u}} (q : K ⟶ T) (L : K.Opens)

/-- The open complement of the closure of the image of all bad source points. -/
def locus : T.Opens := ⟨(closure (q '' (L : Set K)ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Every point above the constructed target open lies in the given source open. -/
theorem preimage_le : q ⁻¹ᵁ locus q L ≤ L := by
  intro x hx
  by_contra hxL
  exact hx (subset_closure ⟨x, hxL, rfl⟩)

/-- Every other target open whose whole inverse image is good lies in this one. -/
theorem le_locus (U : T.Opens) (hU : q ⁻¹ᵁ U ≤ L) : U ≤ locus q L := by
  intro x hx
  change x ∉ closure (q '' (L : Set K)ᶜ)
  intro h
  obtain ⟨y, hy, ⟨z, hz, rfl⟩⟩ :=
    (mem_closure_iff.mp h) U U.isOpen hx
  exact hz (hU hy)

/-- The defining property is equivalent to containment, with the full fiber retained. -/
theorem le_locus_iff (U : T.Opens) : U ≤ locus q L ↔ q ⁻¹ᵁ U ≤ L :=
  ⟨fun h ↦ (q.preimage_mono h).trans (preimage_le q L), le_locus q L U⟩

/-- Increasing the known good open increases the constructed target open. -/
theorem monotone {L₁ L₂ : K.Opens} (h : L₁ ≤ L₂) : locus q L₁ ≤ locus q L₂ :=
  le_locus q L₂ _ ((preimage_le q L₁).trans h)

/-- A completely good source gives the entire original target, including empty fibers. -/
theorem locus_top : locus q ⊤ = ⊤ := by
  apply top_le_iff.mp
  exact le_locus q ⊤ ⊤ le_top

/-- The whole-fiber construction respects intersections of independent good loci. -/
theorem locus_inf (L₁ L₂ : K.Opens) : locus q (L₁ ⊓ L₂) = locus q L₁ ⊓ locus q L₂ := by
  apply le_antisymm
  · exact le_inf (monotone q inf_le_left) (monotone q inf_le_right)
  · apply le_locus q (L₁ ⊓ L₂)
    exact le_inf ((q.preimage_mono inf_le_left).trans (preimage_le q L₁))
      ((q.preimage_mono inf_le_right).trans (preimage_le q L₂))

end FLT.Mazur.SchemeWholeFiberOpen
