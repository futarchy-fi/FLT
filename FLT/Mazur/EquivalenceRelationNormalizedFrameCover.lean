/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts
public import FLT.Mazur.GeometricPointCoverCriterion
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# An actual etale covering family of normalized full relation frames

Allowing all finite sizes and distinguished labels covers the original endpoint
scheme. Complete geometric lifts prove coverage. Members of this cover still
contain incomplete frames; completeness is not asserted to hold everywhere.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Normalized full relation frames cover every original endpoint. -/
theorem normalizedFrames_covers (x : A) :
    ∃ (j : Σ n : ℕ, Fin n) (y : source p q (Fin j.1) j.2),
      first p q (Fin j.1) j.2 y = x := by
  apply GeometricPointCoverCriterion.covers
    (fun j : Σ n : ℕ, Fin n ↦ first p q (Fin j.1) j.2) _ x
  intro K _ _ b
  obtain ⟨n, o, u, hu, _⟩ := exists_complete_normalized_lift e b
  exact ⟨⟨n, o⟩, u, hu⟩

/-- The covering maps are actual etale first projections of the normalized full frames. -/
def normalizedFramesCover : Scheme.Cover (Scheme.precoverage @Etale) A :=
  Scheme.Cover.mkOfCovers (Σ n : ℕ, Fin n)
    (fun j ↦ source p q (Fin j.1) j.2) (fun j ↦ first p q (Fin j.1) j.2)
    (normalizedFrames_covers e) (fun j ↦ first_etale e (Fin j.1) j.2)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
