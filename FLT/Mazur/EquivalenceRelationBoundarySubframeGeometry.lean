/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundarySubframe

/-!
# Cartesian boundary transport under arbitrary subframe selection

Selection factors into an invertible label change followed by a selection fixing
the first endpoint. Both squares are Cartesian. Thus every mixed-size selection
preserves the full pulled-back boundary ideal, without completeness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)

/-- Selection fixing the first endpoint gives an exact square of pulled-back boundaries. -/
theorem stationarySubframeBoundary_isPullback (ι : J ↪ I) :
    IsPullback (subframeBoundaryMap e (ι o') o' i z r s hr hs ι)
      (inclusion I (ι o') i) (inclusion J o' i) (subframeMap e (ι o') o' ι) := by
  have he : subframeMap e (ι o') o' ι ≫ first p q J o' = first p q I (ι o') := by
    rw [subframeMap_first, ← first_eq_distinguished]
  have hb : subframeBoundaryMap e (ι o') o' i z r s hr hs ι ≫ endpoint J o' i =
      endpoint I (ι o') i := by
    apply (cancel_mono i).mp
    rw [Category.assoc, ← endpoint_condition, subframeBoundaryMap_inclusion_assoc,
      he, endpoint_condition]
  apply IsPullback.of_right (h₁₂ := endpoint J o' i) (h₂₂ := first p q J o')
  · rw [hb, he]
    exact (IsPullback.of_hasPullback (first p q I (ι o')) i).flip
  · exact subframeBoundaryMap_inclusion e (ι o') o' i z r s hr hs ι
  · exact (IsPullback.of_hasPullback (first p q J o') i).flip

/-- Arbitrary moving subframes preserve the exact original boundary by base change. -/
theorem subframeBoundaryMap_isPullback (ι : J ↪ I) :
    IsPullback (subframeBoundaryMap e o o' i z r s hr hs ι)
      (inclusion I o i) (inclusion J o' i) (subframeMap e o o' ι) := by
  have h := (labelMap_isPullback e I o (ι o') i z r s hr hs).paste_horiz
    (stationarySubframeBoundary_isPullback e o' i z r s hr hs ι)
  rw [← subframeBoundaryMap_label, subframeBoundaryMap_comp,
    ← subframeMap_label, subframeMap_comp] at h
  exact h

include hr hs in
/-- Factoring through the closed scheme is equivalent before and after mixed-size selection. -/
theorem factors_subframe_iff {T : Scheme.{0}} (a : T ⟶ source p q I o) (ι : J ↪ I) :
    (∃ v : T ⟶ boundary (p := p) (q := q) J o' i,
      v ≫ inclusion J o' i = a ≫ subframeMap e o o' ι) ↔
        ∃ v : T ⟶ boundary (p := p) (q := q) I o i, v ≫ inclusion I o i = a := by
  constructor
  · rintro ⟨v, hv⟩
    let H := subframeBoundaryMap_isPullback e o o' i z r s hr hs ι
    exact ⟨H.lift v a hv, H.lift_snd v a hv⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v ≫ subframeBoundaryMap e o o' i z r s hr hs ι,
      by rw [Category.assoc, subframeBoundaryMap_inclusion, Category.assoc]⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
