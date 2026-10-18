/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundarySubframeCover

/-!
# Faithful detection of boundary differences on selected covers

The full boundary pullback of a selected etale cover detects equality of
arbitrary boundary restrictions, including scaled lifts and nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J) (ι : J ↪ I)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
local notation "jU" => inclusion (p := p) (q := q) I o i
local notation "jV" => inclusion (p := p) (q := q) J o' i
local notation "g" => subframeRefinementMap e o o' ι U V hUV
local notation "b" => subframeBoundaryRefinementMap e o o' ι i z r s hr hs U V hUV
attribute [local irreducible] boundary inclusion endpoint subframeMap subframeBoundaryMap

variable [Etale p]

variable [Surjective (subframeRefinementMap e o o' ι U V hUV)]

include hr hs

/-- An actual selected cover detects equality of arbitrary target boundary restrictions. -/
theorem subframeBoundaryRefinement_eq_iff (v w : Γ(V.toScheme, ⊤)) :
    ((jV) ∣_ V).appTop v = ((jV) ∣_ V).appTop w ↔
      ((jU) ∣_ U).appTop ((g).appTop v) =
        ((jU) ∣_ U).appTop ((g).appTop w) := by
  have hv : (b).appTop (((jV) ∣_ V).appTop v) =
      ((jU) ∣_ U).appTop ((g).appTop v) := by
    change (b ≫ ((jV) ∣_ V)).appTop v = (((jU) ∣_ U) ≫ g).appTop v
    rw [subframeBoundaryRefinement_square]
  have hw : (b).appTop (((jV) ∣_ V).appTop w) =
      ((jU) ∣_ U).appTop ((g).appTop w) := by
    change (b ≫ ((jV) ∣_ V)).appTop w = (((jU) ∣_ U) ≫ g).appTop w
    rw [subframeBoundaryRefinement_square]
  rw [← hv, ← hw]
  exact (subframeBoundaryRefinement_appTop_injective
    e o o' ι i z r s hr hs U V hUV).eq_iff.symm

/-- The full source boundary detects the exact target boundary kernel. -/
theorem subframeBoundaryRefinement_kernel_iff (v : Γ(V.toScheme, ⊤)) :
    ((jV) ∣_ V).appTop v = 0 ↔
      ((jU) ∣_ U).appTop ((g).appTop v) = 0 := by
  simpa only [map_zero] using subframeBoundaryRefinement_eq_iff
    e o o' ι i z r s hr hs U V hUV v 0

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
