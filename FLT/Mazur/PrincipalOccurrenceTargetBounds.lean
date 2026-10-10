/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceExistence

/-!
# Sharing target bounds across incoming occurrences

Each incoming occurrence can request finitely many target relations. Their
finite union gives one bound per shared chart, including charts with no incoming leg.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)] {dst : ∀ i, J i → κ}

/-- A requested relation set, viewed in the fiber over its actual target. -/
def principalOccurrenceIncomingBound
    (q : ∀ i e, Finset (relationIdeal R (B (dst i e)))) (j : κ)
    (e : PrincipalIncoming (dst := dst) j) : Finset (relationIdeal R (B j)) := by
  obtain ⟨⟨i, k⟩, rfl⟩ := e
  exact q i k

variable [Finite ι] [∀ i, Finite (J i)]

/-- All requests fit in common target bounds without changing their shared indexing. -/
theorem exists_principalOccurrence_target_bounds
    (q : ∀ i e, Finset (relationIdeal R (B (dst i e))))
    (s : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ t : ∀ j, Finset (relationIdeal R (B j)), s ≤ t ∧ ∀ i e, q i e ≤ t (dst i e) := by
  classical
  let _ (j : κ) : Fintype (PrincipalIncoming (dst := dst) j) := Fintype.ofFinite _
  let t (j) := s j ∪ Finset.univ.biUnion (principalOccurrenceIncomingBound q j)
  refine ⟨t, fun _ ↦ Finset.subset_union_left, fun i e z hz ↦ ?_⟩
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨⟨i, e⟩, rfl⟩, Finset.mem_univ _, hz⟩

end FLT.Mazur.FiniteTypeRelationModel
