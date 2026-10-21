/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatRelationNormCoefficient
public import FLT.Mazur.FiniteRelationAffineCoreBaseChange
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood

/-!
# Original invariant norm parameters for arbitrary principal domains

The norm is constructed in the original invariant ring, without a chosen
basis. Its principal open is exactly the whole-orbit core of the arbitrary
input parameter. This identity persists under full Cartesian changes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationOriginalNormCore
open SchemeEffectiveEpiSections FiniteFlatRelationNormCoefficient
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{0}} [IsAffine A] [IsAffine D] (p q : D ⟶ A)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The unchanged original norm cuts out the full core of any original parameter. -/
theorem basicOpen_coefficient (a : Γ(A, ⊤)) :
    A.basicOpen (coefficient p q e a).val =
      FiniteRelationAffinePrincipalCore.core (p := p) (q := q) a
        ((isAffineOpen_top A).basicOpen a) := by
  ext x
  exact (mem_basicOpen_coefficient p q e a x).trans
    (FiniteRelationAffinePrincipalCore.mem_core_iff e a _ x).symm

/-- The constructed original invariant parameter refines the original arbitrary domain. -/
theorem basicOpen_coefficient_le (a : Γ(A, ⊤)) :
    A.basicOpen (coefficient p q e a).val ≤ A.basicOpen a := by
  rw [basicOpen_coefficient]
  exact FiniteRelationAffinePrincipalCore.core_le _ _

variable {D' A' : Scheme.{0}} (p' q' : D' ⟶ A')
  [IsFinite p'] [Flat p'] [LocallyOfFinitePresentation p']
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (f : A' ⟶ A) (g : D' ⟶ D) (H : IsPullback g p' p f)
  (hq : g ≫ q = q' ≫ f)

include e' H hq in
/-- A nonaffine Cartesian source has a core cut out by the same original scalar. -/
theorem core_eq_basicOpen_pullback (a : Γ(A, ⊤))
    (ha : IsAffineOpen (A'.basicOpen (f.appTop a))) :
    FiniteRelationAffinePrincipalCore.core (p := p') (q := q') (f.appTop a) ha =
      A'.basicOpen (f.appTop (coefficient p q e a).val) := by
  rw [← FiniteRelationAffinePrincipalCore.core_preimage e e' f g H hq a
    ((isAffineOpen_top A).basicOpen a) ha, ← basicOpen_coefficient,
    Scheme.preimage_basicOpen_top]

end FLT.Mazur.FiniteRelationOriginalNormCore
