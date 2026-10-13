/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeWholeFiberOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Whole-fiber opens commute with open base change

The image of the complete bad fiber locus commutes with scheme pullbacks.
Closure commutes with inverse image along an open continuous map. Together
these prove exact base-change compatibility of the constructed target open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeWholeFiberOpen
variable {K T K' T' : Scheme.{u}} (q : K ⟶ T) (a : K' ⟶ K)
  (q' : K' ⟶ T') (t : T' ⟶ T) (h : IsPullback a q' q t) (L : K.Opens)

include h in
/-- The entire bad locus, including all points of each fiber, commutes with pullback. -/
theorem badImage_baseChange :
    q' '' ((a ⁻¹ᵁ L : K'.Opens) : Set K')ᶜ = t ⁻¹' (q '' (L : Set K)ᶜ) :=
  Scheme.image_preimage_eq_of_isPullback h (L : Set K)ᶜ

include h in
/-- Exact compatibility holds for every open target change, without properness. -/
theorem locus_baseChange (ht : IsOpenMap t) :
    locus q' (a ⁻¹ᵁ L) = t ⁻¹ᵁ locus q L := by
  apply SetLike.coe_injective
  change (closure (q' '' ((a ⁻¹ᵁ L : K'.Opens) : Set K')ᶜ))ᶜ =
    t ⁻¹' (closure (q '' (L : Set K)ᶜ))ᶜ
  rw [badImage_baseChange q a q' t h L,
    ← ht.preimage_closure_eq_closure_preimage t.continuous]
  rfl

include h in
/-- Flat finite-presentation target refinements preserve precisely the same good fibers. -/
theorem locus_flat_baseChange [Flat t] [LocallyOfFinitePresentation t] :
    locus q' (a ⁻¹ᵁ L) = t ⁻¹ᵁ locus q L :=
  locus_baseChange q a q' t h L t.isOpenMap

include h in
/-- Coverage by the whole-fiber open can be tested after a surjective open base change. -/
theorem locus_top_iff_baseChange (ht : IsOpenMap t) [Surjective t] :
    locus q' (a ⁻¹ᵁ L) = ⊤ ↔ locus q L = ⊤ := by
  rw [locus_baseChange q a q' t h L ht]
  constructor
  · intro he
    apply top_le_iff.mp
    intro x _
    obtain ⟨y, rfl⟩ := t.surjective x
    have hy : y ∈ t ⁻¹ᵁ locus q L := by rw [he]; trivial
    exact hy
  · intro he
    rw [he]
    rfl

end FLT.Mazur.SchemeWholeFiberOpen
