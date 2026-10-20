/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationPrincipalBoundaryPatching
public import FLT.Mazur.FiniteProjectiveRelationIntegralCoordinates
public import FLT.Mazur.FiniteFlatGlobalSections
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Geometric principal covers construct invariant boundary lifts

Integrality of the full finite locally free relation descends a geometric
cover's unit ideal to the invariant coefficients. Thus the patching theorem
needs only a cover of the actual affine source, not a supplied invariant
partition of unity or Noetherianity of the invariant ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationPrincipalBoundaryCover
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
open SchemeFiniteGroupQuotient SchemeRelationPrincipalBoundaryNumerator
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
variable {D X Y : Scheme.{0}} (p q : D ⟶ X) [IsAffine X] [IsAffine D]
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type*} (r : ι → compatibleFunctions p q)

include e in
/-- A geometric principal cover generates one in the actual full invariant ring. -/
theorem invariant_span_of_cover (hr : (⨆ j, X.basicOpen (r j).val) = ⊤) :
    Ideal.span (Set.range r) = ⊤ := by
  have hi := FiniteProjectiveRelationIntegralCoordinates.invariant_inclusion_integral
    p q e p.finite_appTop (FCurve.finiteFlat_appTop_projective p)
  apply (Ideal.map_eq_top_iff (compatibleFunctions p q).subtype Subtype.val_injective hi).mp
  rw [Ideal.map_span, ← Set.range_comp]
  apply (isAffineOpen_top X).iSup_basicOpen_eq_self_iff.mp
  apply top_unique
  intro x _
  have hx : x ∈ ⨆ j, X.basicOpen (r j).val := by rw [hr]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(r j).val, ⟨j, rfl⟩⟩, hj⟩

variable [Finite ι] (i : Y ⟶ X) [IsAffine Y]
local notation "U" j => X.basicOpen (r j).val
local notation "hU" j => compatibleFunctions_basicOpen p q (r j)

include e in
/-- Independent local boundary lifts on a geometric finite cover give a full invariant lift. -/
theorem exists_boundary_lift (hr : (⨆ j, U j) = ⊤)
    (v : ∀ j, coefficients p q (U j) (hU j)) (t : Γ(Y, ⊤))
    (hv : ∀ j, (principalPullbackMap i (r j).val).appTop (v j).val =
      (Y.basicOpen (i.appTop (r j).val)).ι.appTop t) :
    ∃ w : compatibleFunctions p q, i.appTop w.val = t :=
  exists_boundary_lift_of_span p q i r (invariant_span_of_cover p q e r hr) v t hv

end FLT.Mazur.FiniteRelationPrincipalBoundaryCover
