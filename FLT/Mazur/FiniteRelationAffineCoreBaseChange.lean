/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationAffinePrincipalCore

/-!
# Exact base change of whole-orbit affine norm cores

Although norm coefficients depend on the finite locally free presentation,
their affine core opens commute with every cartesian change of full relations.
The proof lifts each original arrow through the entire first-endpoint square.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationAffinePrincipalCore
set_option backward.isDefEq.respectTransparency false
variable {D A D' A' : Scheme} {p q : D ⟶ A} {p' q' : D' ⟶ A'}
  (e : CategoryTheory.EquivalenceRelation p q) (e' : CategoryTheory.EquivalenceRelation p' q')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)

include H hq in
/-- Whole-fiber containment pulls back through the complete cartesian relation square. -/
theorem wholeFiber_baseChange (W : Set A) (x : A') :
    (∀ z : D, p z = a x → q z ∈ W) ↔
      ∀ z : D', p' z = x → a (q' z) ∈ W := by
  constructor
  · intro h z hz
    have hp : p (b z) = a x :=
      (congrArg (fun g ↦ g z) H.w).trans (congrArg a hz)
    have hs : q (b z) = a (q' z) := congrArg (fun g ↦ g z) hq
    exact hs ▸ h (b z) hp
  · intro h z hz
    obtain ⟨w, hw, hw'⟩ := Scheme.exists_preimage_of_isPullback H z x hz
    have hs : q z = a (q' w) := by
      rw [← hw]
      exact congrArg (fun g ↦ g w) hq
    exact hs ▸ h w hw'

variable [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  [IsFinite p'] [Flat p'] [LocallyOfFinitePresentation p']
  (s : Γ(A, ⊤)) (hs : IsAffineOpen (A.basicOpen s))
  (hs' : IsAffineOpen (A'.basicOpen (a.appTop s)))

include H hq in
include e e' in
/-- Canonical affine cores commute with the exact source transition, including nonflat ones. -/
theorem core_preimage : a ⁻¹ᵁ core (p := p) (q := q) s hs =
    core (p := p') (q := q') (a.appTop s) hs' := by
  ext x
  change a x ∈ core (p := p) (q := q) s hs ↔
    x ∈ core (p := p') (q := q') (a.appTop s) hs'
  rw [mem_core_iff e, mem_core_iff e']
  rw [← Scheme.preimage_basicOpen_top]
  exact wholeFiber_baseChange a b H hq _ x

end FLT.Mazur.FiniteRelationAffinePrincipalCore
