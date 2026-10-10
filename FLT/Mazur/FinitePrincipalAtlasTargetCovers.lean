/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOccurrences

/-!
# Target-compatible covers in the original affine atlas

The selected occurrence data covers every full pairwise chart intersection.
Consequently any overlap contained in a target chart is covered by exactly
those occurrences whose shared labels also occur in that target chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {X : Scheme.{u}} [QuasiSeparatedSpace X] {ι : Type v} (U : ι → X.affineOpens)

/-- A shared overlap lies in every chart in which it has an occurrence. -/
theorem atlasPrincipalOpen_le_occurrence (i : ι) (k : AtlasPrincipalOccurrence U i) :
    (atlasPrincipalOpen U (atlasPrincipalDestination U i k)).1 ≤ (U i).1 := by
  rw [← atlasPrincipalSection_open]
  exact X.basicOpen_le _

/-- Target-compatible occurrences cover precisely the ambient chart intersection. -/
theorem atlasPrincipal_target_cover (i t : ι) :
    (⨆ l : {l : AtlasPrincipalOccurrence U i //
      ∃ k : AtlasPrincipalOccurrence U t,
        atlasPrincipalDestination U t k = atlasPrincipalDestination U i l},
      X.basicOpen (atlasPrincipalSection U i l.val)) = (U i).1 ⊓ (U t).1 := by
  apply le_antisymm
  · apply iSup_le
    intro l
    obtain ⟨k, hk⟩ := l.property
    refine le_inf (X.basicOpen_le _) ?_
    rw [atlasPrincipalSection_open, ← hk]
    exact atlasPrincipalOpen_le_occurrence U t k
  · rw [← atlasPrincipalPairs_cover U i t]
    apply iSup_le
    intro p
    exact le_iSup_of_le ⟨⟨t, .inl p⟩, ⟨⟨i, .inr p⟩, rfl⟩⟩ le_rfl

/-- Containment in a target chart proves the required original occurrence cover inclusion. -/
theorem atlasPrincipal_occurrence_target_cover (i t : ι) (k : AtlasPrincipalOccurrence U i)
    (h : (atlasPrincipalOpen U (atlasPrincipalDestination U i k)).1 ≤ (U t).1) :
    X.basicOpen (atlasPrincipalSection U i k) ≤
      ⨆ l : {l : AtlasPrincipalOccurrence U i //
        ∃ n : AtlasPrincipalOccurrence U t,
          atlasPrincipalDestination U t n = atlasPrincipalDestination U i l},
        X.basicOpen (atlasPrincipalSection U i l.val) := by
  rw [atlasPrincipal_target_cover]
  exact le_inf (X.basicOpen_le _) ((atlasPrincipalSection_open U i k).symm ▸ h)

/-- All occurrences in each chart cover that entire chart, using the diagonal pair. -/
theorem atlasPrincipal_occurrences_cover (i : ι) :
    (⨆ k : AtlasPrincipalOccurrence U i, X.basicOpen (atlasPrincipalSection U i k)) =
      (U i).1 := by
  apply le_antisymm (iSup_le fun _ ↦ X.basicOpen_le _)
  calc
    (U i).1 = ⨆ p : atlasPrincipalPairs U i i, X.basicOpen p.val.1 := by
      rw [atlasPrincipalPairs_cover, inf_idem]
    _ ≤ _ := iSup_le fun p ↦ le_iSup_of_le ⟨i, .inl p⟩ le_rfl

end FLT.Mazur.Approximation
