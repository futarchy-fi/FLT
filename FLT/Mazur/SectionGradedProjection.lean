/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedLinePullback

/-!
# Homogeneous projections and actual section pullbacks

Projection onto a tensor degree commutes with pullback along a specified line
comparison. This gives degreewise projections on compatible formal sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.SectionGradedSum

open SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) (U : X.Opens)

/-- Projection onto a homogeneous summand, viewed inside the full section ring. -/
def projectDegree (k : ℕ) : Sections L U →ₗ[Γ(X, U)] Sections L U :=
  (of L U k).comp (DirectSum.component Γ(X, U) ℕ (Piece L U) k)

/-- Projection selects exactly the specified homogeneous summand. -/
theorem projectDegree_of (k j : ℕ) (s : Piece L U j) :
    projectDegree L U k (of L U j s) = if j = k then of L U j s else 0 := by
  by_cases hj : j = k
  · subst j
    simp [projectDegree, DirectSum.component.lof_self]
  · simp [projectDegree, DirectSum.component.of, hj]

/-- Every projected section belongs to the specified homogeneous submodule. -/
theorem projectDegree_mem (k : ℕ) (s : Sections L U) :
    projectDegree L U k s ∈ grade L U k := ⟨_, rfl⟩

/-- Projection acts by identity or zero on an arbitrary homogeneous section. -/
theorem projectDegree_of_mem (k j : ℕ) (s : Sections L U) (hs : s ∈ grade L U j) :
    projectDegree L U k s = if j = k then s else 0 := by
  obtain ⟨t, rfl⟩ := hs
  exact projectDegree_of L U k j t

variable {Y : Scheme} (f : X ⟶ Y) {L' : Y.Modules} {M : X.Modules}
    (e : (pullback f).obj L' ≅ M)

/-- Actual section pullback commutes with projection onto every tensor degree. -/
theorem projectDegree_pullback (k : ℕ) (s : Sections L' ⊤) :
    projectDegree M ⊤ k (SectionGradedLinePullback.ringHom f e s) =
      SectionGradedLinePullback.ringHom f e (projectDegree L' ⊤ k s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j s =>
    change projectDegree M ⊤ k (SectionGradedLinePullback.ringHom f e (of L' ⊤ j s)) =
      SectionGradedLinePullback.ringHom f e (projectDegree L' ⊤ k (of L' ⊤ j s))
    rw [projectDegree_of, SectionGradedLinePullback.ringHom_of, projectDegree_of]
    split_ifs
    · exact (SectionGradedLinePullback.ringHom_of f e j s).symm
    · exact (map_zero _).symm
  | add s t hs ht => simp only [map_add, hs, ht]

end FLT.Mazur.SectionGradedSum
