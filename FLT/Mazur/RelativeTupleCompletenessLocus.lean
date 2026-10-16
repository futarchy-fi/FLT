/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeTupleSections
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The residual scheme and the exact completeness locus

The complement of the enumerated sections is an actual clopen subscheme of
the full pullback. Its image is open because the original source is etale.
Thus complete frames form a closed set; this does not assert that completeness
extends to an open neighborhood of a complete geometric fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I]

/-- The full residual source, retaining its original scheme structure. -/
def residualOpen : (framedSource E I).Opens :=
  ⟨(enumeratedOpen E I : Set _)ᶜ, (enumeratedOpen_isClosed E I).isOpen_compl⟩

/-- The residual scheme maps to the unchanged ordered-point scheme. -/
def residualProjection : (residualOpen E I).toScheme ⟶ (distinctScheme E I).left :=
  (residualOpen E I).ι ≫ framedProjection E I

instance residualProjection_etale : Etale (residualProjection E I) := by
  unfold residualProjection
  infer_instance

/-- The residual inclusion is closed as well as open. -/
theorem residualOpen_isClosed : IsClosed (residualOpen E I : Set (framedSource E I)) :=
  (enumeratedOpen E I).isOpen.isClosed_compl

/-- Frames failing to enumerate the entire original pullback. -/
def incompleteOpen : (distinctScheme E I).left.Opens :=
  ⟨Set.range (residualProjection E I), (residualProjection E I).isOpenMap.isOpen_range⟩

/-- Completeness refers to every point of the full original framed source. -/
def completeLocus : Set (distinctScheme E I).left := (incompleteOpen E I : Set _)ᶜ

/-- Etale geometry makes the completeness locus closed, without making it open. -/
theorem completeLocus_isClosed : IsClosed (completeLocus E I) :=
  (incompleteOpen E I).isOpen.isClosed_compl

/-- Exact completeness is equivalent to absence of any residual point over the frame. -/
theorem mem_completeLocus (x : (distinctScheme E I).left) :
    x ∈ completeLocus E I ↔
      ∀ y : framedSource E I, framedProjection E I y = x → y ∈ enumeratedOpen E I := by
  constructor
  · intro hx y hy
    by_contra hn
    apply hx
    exact ⟨⟨y, hn⟩, hy⟩
  · intro hx ⟨y, hy⟩
    exact y.property (hx y.val hy)

/-- On a complete fiber, each full-source point is one of the actual universal sections. -/
theorem mem_completeLocus_iff_sections (x : (distinctScheme E I).left) :
    x ∈ completeLocus E I ↔
      ∀ y : framedSource E I, framedProjection E I y = x →
        ∃ i, framedSection E I i x = y := by
  rw [mem_completeLocus]
  constructor
  · intro hx y hy
    simpa only [hy] using (mem_enumeratedOpen E I y).mp (hx y hy)
  · intro hx y hy
    apply (mem_enumeratedOpen E I y).mpr
    simpa only [hy] using hx y hy

end FLT.Mazur.RelativeOrderedTuples
