/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeTupleCompletenessLocus
public import FLT.Mazur.SchemeFiniteFiberInterior

/-!
# Open complete frames on the finite locus of the whole framed source

Completeness becomes open wherever the original framed projection is finite
on a neighborhood. The finite locus is constructed from the whole projection,
not from the enumerated sections or a selected part of the fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I]

/-- Complete frames whose entire framed projection is finite nearby. -/
def finiteCompleteOpen : (distinctScheme E I).left.Opens :=
  finiteTargetOpen (framedProjection E I) ⊓
    fullFiberInterior (framedProjection E I) (enumeratedOpen E I)

/-- No completeness is lost on this actual finite locus. -/
theorem mem_finiteCompleteOpen (x : (distinctScheme E I).left) :
    x ∈ finiteCompleteOpen E I ↔
      x ∈ finiteTargetOpen (framedProjection E I) ∧ x ∈ completeLocus E I := by
  constructor
  · rintro ⟨hf, hc⟩
    refine ⟨hf, (mem_completeLocus E I x).mpr ?_⟩
    exact (mem_fullFiberLocus _ _ x).mp (fullFiberInterior_subset _ _ hc)
  · rintro ⟨hf, hc⟩
    exact ⟨hf, mem_fullFiberInterior_of_finiteTarget _ _ x hf
      ((mem_completeLocus E I x).mp hc)⟩

/-- The constructed open consists of complete frames for the unchanged full fiber. -/
theorem finiteCompleteOpen_subset :
    (finiteCompleteOpen E I : Set _) ⊆ completeLocus E I :=
  fun x hx ↦ ((mem_finiteCompleteOpen E I x).mp hx).2

/-- Global finiteness of the original source makes its full framed projection finite. -/
instance framedProjection_finite [IsFinite E.hom] : IsFinite (framedProjection E I) :=
  inferInstanceAs (IsFinite (pullback.snd E.hom (distinctScheme E I).hom))

/-- For a finite etale source, the constructed open contains every complete frame. -/
theorem finiteCompleteOpen_eq_completeLocus [IsFinite E.hom] :
    (finiteCompleteOpen E I : Set _) = completeLocus E I := by
  ext x
  change x ∈ finiteCompleteOpen E I ↔ x ∈ completeLocus E I
  rw [mem_finiteCompleteOpen, finiteTargetOpen_eq_top]
  simp only [Opens.mem_top, true_and]

/-- Completeness is both open and closed for an actually finite etale source. -/
theorem completeLocus_isOpen_of_finite [IsFinite E.hom] : IsOpen (completeLocus E I) := by
  rw [← finiteCompleteOpen_eq_completeLocus E I]
  exact (finiteCompleteOpen E I).isOpen

end FLT.Mazur.RelativeOrderedTuples
