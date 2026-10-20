/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationAffinePrincipalCore
public import FLT.Mazur.SchemeRelationInvariantSpectrum

/-!
# Original invariant principal domains are already whole-orbit cores

For an invariant original scalar, taking the whole-orbit core does not
shrink its principal open. No norm or replacement scalar is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationAffinePrincipalCore
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
variable {D A : Scheme.{0}} {p q : D ⟶ A}
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- The principal open of an original invariant scalar retains every original arrow. -/
theorem core_eq_basicOpen_of_invariant (s : compatibleFunctions p q)
    (hs : IsAffineOpen (A.basicOpen s.val)) :
    core (p := p) (q := q) s.val hs = A.basicOpen s.val := by
  apply le_antisymm (core_le s.val hs)
  intro x hx
  apply (mem_core_iff e s.val hs x).mpr
  intro z hz
  have hp : z ∈ p ⁻¹ᵁ A.basicOpen s.val := by
    change p z ∈ A.basicOpen s.val
    rwa [hz]
  rw [compatibleFunctions_basicOpen p q s] at hp
  exact hp

end FLT.Mazur.FiniteRelationAffinePrincipalCore
