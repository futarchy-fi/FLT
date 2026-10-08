/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedRestriction

/-!
# Homogeneous projections of the original coefficient presheaf

Projection to each actual graded quotient is linear for the original
structure sheaf and commutes with restriction on every open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- Extract one actual homogeneous coefficient with its original scalar action. -/
def component (U : X.Opens) (n : ℕ) : Sections I U →ₗ[Γ(X, U)] Piece I U n :=
  DirectSum.component Γ(X, U) ℕ (Piece I U) n

omit [IsLocallyNoetherian X] in
/-- Homogeneous extraction is a left inverse to the original inclusion. -/
lemma component_of (U : X.Opens) (n : ℕ) (s : Piece I U n) :
    component I U n (of I U n s) = s :=
  DirectSum.component.lof_self _ _ _

/-- Restriction commutes with extraction of each homogeneous coefficient. -/
lemma component_restrict {U V : X.Opens} (i : U ⟶ V) (n : ℕ) (s : Sections I V) :
    component I U n (restrictRingHom I U i s) =
      (idealGraded I n).presheaf.map i.op (component I V n s) := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | of m s =>
    change component I U n (restrict I U i (of I V m s)) =
      (idealGraded I n).presheaf.map i.op (component I V n (of I V m s))
    rw [restrict_of]
    by_cases h : m = n
    · subst m
      rw [component_of, component_of]
    · simp only [component, DirectSum.component.of, h, ↓reduceDIte, map_zero]

end FLT.Mazur.IdealAdicGradedSections
