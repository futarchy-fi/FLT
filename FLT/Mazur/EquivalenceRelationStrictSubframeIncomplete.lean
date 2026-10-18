/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSubframe
public import FLT.Mazur.EquivalenceRelationCompletePointLocus
public import FLT.Mazur.EquivalenceRelationBoundarySubframe

/-!
# Strict subframes remain on the original boundary but are incomplete

Deleting at least one label from any normalized frame produces an incomplete
frame. The same construction preserves the exact original invariant boundary.
Thus boundary membership alone cannot certify completeness of smaller frames.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (ι : J ↪ I) (hlt : Fintype.card J < Fintype.card I)

include hlt

/-- Any strict subframe misses an original arrow, even when the larger frame is incomplete. -/
theorem strict_subframe_not_complete {K : Type} [Field K]
    (u : Spec (.of K) ⟶ source p q I o) :
    ¬ Complete J o' (u ≫ subframeMap e o o' ι) := by
  intro hc
  apply Nat.not_le_of_lt hlt
  apply original_arrow_cardinality_le e o' o (u ≫ subframeMap e o o' ι) u hc
    (u ≫ coordinate p q I o (ι o') ≫ e.s)
  · simp only [Category.assoc, e.symmetry₁, subframeMap_first]
  · simp only [Category.assoc, e.symmetry₂, coordinate_first]

/-- Strict selection sends every original point outside the entire complete locus. -/
theorem strict_subframe_point_incomplete (x : source p q I o) :
    subframeMap e o o' ι x ∉ completePointLocus (p := p) (q := q) J o' := by
  have h := strict_subframe_not_complete e o o' ι hlt
    ((source p q I o).fromSpecResidueField x)
  rw [complete_iff_mem_completePointLocus] at h
  have hx : (source p q I o).fromSpecResidueField x default = x :=
    Scheme.fromSpecResidueField_apply x default
  change subframeMap e o o' ι ((source p q I o).fromSpecResidueField x default) ∉ _ at h
  exact fun hc ↦ h ((congrArg (fun y ↦ subframeMap e o o' ι y ∈
    completePointLocus (p := p) (q := q) J o') hx).to_iff.mpr hc)

namespace InvariantBoundary
variable {B C : Scheme.{0}} (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)

/-- The exact boundary retains strict subframes, which are still intrinsically incomplete. -/
theorem strict_boundary_subframe_incomplete (x : boundary (p := p) (q := q) I o i) :
    inclusion J o' i (subframeBoundaryMap e o o' i z r s hr hs ι x) ∉
      completePointLocus (p := p) (q := q) J o' := by
  have he := congrArg (fun f ↦ f x)
    (subframeBoundaryMap_inclusion e o o' i z r s hr hs ι)
  change inclusion J o' i (subframeBoundaryMap e o o' i z r s hr hs ι x) =
    subframeMap e o o' ι (inclusion I o i x) at he
  rw [he]
  exact strict_subframe_point_incomplete e o o' ι hlt _

include e ι z r s hr hs in
/-- A nonempty larger boundary supplies an actual incomplete smaller boundary point. -/
theorem exists_incomplete_boundary_of_strict_subframe
    (x : boundary (p := p) (q := q) I o i) :
    ∃ y : boundary (p := p) (q := q) J o' i,
      inclusion J o' i y ∉ completePointLocus (p := p) (q := q) J o' :=
  ⟨subframeBoundaryMap e o o' i z r s hr hs ι x,
    strict_boundary_subframe_incomplete e o o' ι hlt i z r s hr hs x⟩

end InvariantBoundary
end FLT.Mazur.EquivalenceRelationNormalizedFrames
