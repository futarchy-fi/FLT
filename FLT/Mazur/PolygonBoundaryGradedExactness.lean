/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryGradedParameter
public import FLT.Mazur.PolygonBoundaryScalarExactness

/-!
# Actual homogeneous adjacent kernels over the complete coefficient base

Above one uniform degree bound, an actual homogeneous section restricts to
zero exactly when it is a last-parameter-power multiple of another section
of the same degree. The multiplication is that of the original graded ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Homogeneous evaluation kernels are exactly homogeneous complete-base parameter multiples. -/
theorem boundaryGrade_uniformScalarKernel : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : grade (boundaryLine K (m + 1) n h) ⊤ d,
      boundarySectionsMap K n h (homOfLE (Nat.le_succ m)) s.val = 0 ↔
        ∃ t : grade (boundaryLine K (m + 1) n h) ⊤ d,
          boundarySeriesScalars K n h (m + 1) PowerSeries.X ^ (m + 1) * t.val = s.val := by
  obtain ⟨N, hN⟩ := boundarySections_uniformScalarExact K n h
  refine ⟨N, fun d hd m s ↦ ?_⟩
  obtain ⟨s, ⟨u, rfl⟩⟩ := s
  change boundarySectionsMap K n h (homOfLE (Nat.le_succ m))
      (of (boundaryLine K (m + 1) n h) ⊤ d u) = 0 ↔ _
  rw [boundarySectionsMap_adjacent_ringHom, SectionGradedLinePullback.ringHom_of_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (hN d hd m u).mp hz
    refine ⟨⟨of (boundaryLine K (m + 1) n h) ⊤ d v, ⟨v, rfl⟩⟩, ?_⟩
    exact (boundarySeriesScalars_power_of K n h (m + 1) (m + 1) d v).trans
      (congrArg (of (boundaryLine K (m + 1) n h) ⊤ d) hv)
  · rintro ⟨⟨t, ⟨v, rfl⟩⟩, ht⟩
    rw [boundarySeriesScalars_power_of] at ht
    have hv : stageParameterSection K (m + 1) n h ^ (m + 1) • v = u :=
      DirectSum.of_injective d ht
    exact (hN d hd m u).mpr ⟨v, hv⟩

end FLT.Mazur.PolygonInfinitesimalStages
