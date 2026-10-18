/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeTransfer
public import FLT.Mazur.EquivalenceRelationSubframeDiscrepancy

/-!
# Exact boundary formula for unordered-subframe transfer

Every selected target lift has the same original boundary value. The invariant
transfer therefore lifts its binomial multiple. Subtracting the transfer from
the corresponding multiple of an independent invariant source lift gives a
constructed invariant boundary-zero correction, with all nilpotents retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (EquivalenceRelationNormalizedFrames.action e I o σ).hom ⁻¹ᵁ U = U)
  (V : (source p q J o').Opens)
  (hV : ∀ σ, (EquivalenceRelationNormalizedFrames.action e J o' σ).hom ⁻¹ᵁ V = V)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

/-- A canonical invariant correction from independent invariant chart lifts. -/
def subframeTransferCorrection
    (u : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e I o) U hU))
    (v : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e J o') V hV)) :
    invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e I o) U hU) :=
  (Fintype.card I).choose (Fintype.card J) • u - subframeTransfer e o o' U hU V hV h v

/-- The invariant correction is exactly the sum of the raw, possibly noninvariant errors. -/
theorem subframeTransferCorrection_eq_sum
    (u : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e I o) U hU))
    (v : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e J o') V hV)) :
    (subframeTransferCorrection e o o' U hU V hV h u v).val =
      ∑ s : SubframeSelections I (Fintype.card J),
        subframeDiscrepancy e o o' (SubframeSelections.embedding s) U V
          (h (SubframeSelections.embedding s)) u.val v.val := by
  change _ - subframeTransferSection e o o' U V hV h v = _
  simp only [subframeDiscrepancy, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, SubframeSelections.card, subframeTransferSection]
  rfl

namespace InvariantBoundary
variable {B C : Scheme.{0}} (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "jU" => inclusion (p := p) (q := q) I o i
local notation "jV" => inclusion (p := p) (q := q) J o' i
variable (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
  (hUE : (inclusion (p := p) (q := q) I o i ⁻¹ᵁ U) ≤
    endpoint (p := p) (q := q) I o i ⁻¹ᵁ E)
  (hVE : (inclusion (p := p) (q := q) J o' i ⁻¹ᵁ V) ≤
    endpoint (p := p) (q := q) J o' i ⁻¹ᵁ E)

include hr hs in
/-- The transfer lifts the exact binomial multiple on the entire original boundary. -/
theorem subframeTransfer_boundary
    (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (v : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e J o') V hV))
    (hv : ((jV) ∣_ V).appTop v.val =
      ((endpoint J o' i).resLE E (jV ⁻¹ᵁ V) hVE).appTop t) :
    ((jU) ∣_ U).appTop (subframeTransferSection e o o' U V hV h v) =
      (Fintype.card I).choose (Fintype.card J) •
        ((endpoint I o i).resLE E (jU ⁻¹ᵁ U) hUE).appTop t := by
  unfold subframeTransferSection
  rw [map_sum]
  simp only [subframeBoundaryRefinement_lift e o o' _ i z r s hr hs U V _ E hE
    hUE hVE t ht v.val hv, Finset.sum_const, Finset.card_univ, SubframeSelections.card]

include hr hs in
/-- The constructed correction is invariant and vanishes on the unreduced original boundary. -/
theorem subframeTransferCorrection_boundary_zero
    (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (u : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e I o) U hU))
    (v : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e J o') V hV))
    (hu : ((jU) ∣_ U).appTop u.val =
      ((endpoint I o i).resLE E (jU ⁻¹ᵁ U) hUE).appTop t)
    (hv : ((jV) ∣_ V).appTop v.val =
      ((endpoint J o' i).resLE E (jV ⁻¹ᵁ V) hVE).appTop t) :
    ((jU) ∣_ U).appTop (subframeTransferCorrection e o o' U hU V hV h u v).val = 0 := by
  rw [subframeTransferCorrection_eq_sum, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  exact subframeDiscrepancy_boundary_zero e o o' _ U V _ i z r s hr hs E hE
    hUE hVE t ht u.val v.val hu hv

end InvariantBoundary
end FLT.Mazur.EquivalenceRelationNormalizedFrames
