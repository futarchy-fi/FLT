/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeWholeFiberOpen

/-!
# Composing whole-fiber open constructions

Removing bad fibers first over a source and then over its scalar base is
exactly the same as removing them over the composite map. Closedness is
needed only for the particular bad image to replace closure avoidance by
an empty-fiber test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeWholeFiberOpen
variable {K T S : Scheme.{u}} (q : K ⟶ T) (f : T ⟶ S) (L : K.Opens)

/-- Whole-fiber interiors compose, with no closed-map hypothesis. -/
theorem locus_comp : locus (q ≫ f) L = locus f (locus q L) := by
  apply le_antisymm
  · apply le_locus f (locus q L)
    apply le_locus q L
    exact preimage_le (q ≫ f) L
  · apply le_locus (q ≫ f) L
    exact (q.preimage_mono (preimage_le f (locus q L))).trans (preimage_le q L)

/-- Closedness of just the bad image suffices to retain every good fiber. -/
theorem mem_locus_iff_of_badImage_closed (h : IsClosed (q '' (L : Set K)ᶜ)) (x : T) :
    x ∈ locus q L ↔ ∀ y : K, q y = x → y ∈ L := by
  change x ∉ closure (q '' (L : Set K)ᶜ) ↔ _
  rw [h.closure_eq]
  constructor
  · intro hx y hy
    by_contra hyL
    exact hx ⟨y, hyL, hy⟩
  · rintro hx ⟨y, hy, he⟩
    exact hy (hx y he)

/-- A closed composite bad image retains the entire intermediate fiber as well. -/
theorem fiber_subset_locus_of_composite_badImage_closed
    (h : IsClosed ((q ≫ f) '' (L : Set K)ᶜ)) (x : S)
    (hx : ∀ y : K, (q ≫ f) y = x → y ∈ L) :
    ∀ t : T, f t = x → t ∈ locus q L := by
  have hx' := (mem_locus_iff_of_badImage_closed (q ≫ f) L h x).mpr hx
  rw [locus_comp] at hx'
  intro t ht
  apply preimage_le f (locus q L)
  change f t ∈ locus f (locus q L)
  rwa [ht]

end FLT.Mazur.SchemeWholeFiberOpen
