/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundarySubframeRefinement
public import FLT.Mazur.EquivalenceRelationSubframeExchangeMap

/-!
# Subframe exchanges preserve the original boundary kernel

The cartesian boundary construction makes each selected pullback carry the
target boundary kernel into the source boundary kernel. Thus every available
target exchange correction has zero restriction to the unreduced source boundary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
local notation "jU" => inclusion (p := p) (q := q) I o i
local notation "jV" => inclusion (p := p) (q := q) J o' i
attribute [local irreducible] boundary inclusion endpoint subframeMap subframeBoundaryMap
include hr hs

/-- Pulling back along a selected subframe preserves the entire original boundary kernel. -/
theorem subframeBoundaryRefinement_kernel (ι : J ↪ I)
    (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V) (v : Γ(V.toScheme, ⊤))
    (hv : ((jV) ∣_ V).appTop v = 0) :
    ((jU) ∣_ U).appTop ((subframeRefinementMap e o o' ι U V hUV).appTop v) = 0 := by
  change (((jU) ∣_ U) ≫ subframeRefinementMap e o o' ι U V hUV).appTop v = 0
  rw [← subframeBoundaryRefinement_square e o o' ι i z r s hr hs U V hUV]
  change (subframeBoundaryRefinementMap e o o' ι i z r s hr hs U V hUV).appTop
    (((jV) ∣_ V).appTop v) = 0
  rw [hv, map_zero]

variable (hV : ∀ σ, (EquivalenceRelationNormalizedFrames.action e J o' σ).hom ⁻¹ᵁ V = V)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

/-- Every difference of selected target boundary-kernel elements is source boundary-zero. -/
theorem subframeSelectionDifference_boundary_zero (ι κ : J ↪ I)
    (v : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e J o') V hV))
    (hv : ((jV) ∣_ V).appTop v.val = 0) :
    ((jU) ∣_ U).appTop (subframeSelectionDifference e o o' U V hV h ι κ v) = 0 := by
  change ((jU) ∣_ U).appTop
    ((subframeRefinementMap e o o' κ U V (h κ)).appTop v.val -
      (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val) = 0
  rw [map_sub,
    subframeBoundaryRefinement_kernel e o o' i z r s hr hs U V κ (h κ) v.val hv,
    subframeBoundaryRefinement_kernel e o o' i z r s hr hs U V ι (h ι) v.val hv,
    sub_self]

/-- The one-exchange correction operator preserves the actual boundary kernel. -/
theorem subframeExchangeMap_boundary_zero [DecidableEq I] (ι : J ↪ I) (b₀ : I)
    (v : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e J o') V hV))
    (hv : ((jV) ∣_ V).appTop v.val = 0) :
    ((jU) ∣_ U).appTop (subframeExchangeMap e o o' U V hV h ι b₀ v) = 0 :=
  subframeSelectionDifference_boundary_zero e o o' i z r s hr hs U V hV h ι _ v hv

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
