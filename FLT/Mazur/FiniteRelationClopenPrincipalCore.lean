/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationAffinePrincipalCore
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Whole-orbit cores of clopen original principal domains

An open first projection sends the open complement of a clopen principal
domain to an open set of bad orbits. Its complement is the actual whole-orbit
core. Thus closedness of the core is constructed from the original domain;
the original parameter need not be invariant.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationAffinePrincipalCore
variable {D A : Scheme} {p q : D ⟶ A}
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)
  (a : Γ(A, ⊤)) (ha : IsAffineOpen (A.basicOpen a))

include e in
/-- The omitted points are precisely the image of arrows ending outside the original domain. -/
theorem core_compl_eq_image :
    (core (p := p) (q := q) a ha : Set A)ᶜ =
      p '' (q ⁻¹' (A.basicOpen a : Set A)ᶜ) := by
  ext x
  change (¬ x ∈ core (p := p) (q := q) a ha) ↔
    ∃ z, q z ∉ A.basicOpen a ∧ p z = x
  rw [mem_core_iff e]
  push Not
  constructor
  · rintro ⟨z, hz, hn⟩
    exact ⟨z, hn, hz⟩
  · rintro ⟨z, hn, hz⟩
    exact ⟨z, hz, hn⟩

include e in
/-- A clopen original domain gives a clopen full orbit core, without invariant parameters. -/
theorem core_isClosed_of_basicOpen_closed
    (h : IsClosed (A.basicOpen a : Set A)) :
    IsClosed (core (p := p) (q := q) a ha : Set A) := by
  rw [← isOpen_compl_iff, core_compl_eq_image e a ha]
  exact p.isOpenMap _ (h.isOpen_compl.preimage q.continuous)

end FLT.Mazur.FiniteRelationAffinePrincipalCore
