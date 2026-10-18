/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeRefinement
public import FLT.Mazur.EquivalenceRelationBoundaryChartTransport

/-!
# Exact boundary lifts under strict subframe chart refinement

The whole original boundary maps to the smaller frame boundary. Pulling back
an exact lift preserves an arbitrary original invariant open coefficient.
This statement concerns actual sections, without assuming larger-group invariance.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J) (ι : J ↪ I)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
local notation "jU" => inclusion (p := p) (q := q) I o i
local notation "jV" => inclusion (p := p) (q := q) J o' i
local notation "l" => subframeBoundaryMap e o o' i z r s hr hs ι
attribute [local irreducible] boundary inclusion endpoint subframeMap subframeBoundaryMap

include hUV in
/-- The full original boundary remains in the independently supplied target chart. -/
theorem subframeBoundaryRefinement_le : jU ⁻¹ᵁ U ≤ (l) ⁻¹ᵁ (jV ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_inclusion, Scheme.Hom.comp_preimage]
  exact (jU).preimage_mono hUV

/-- The induced morphism of exact boundary charts for any subframe size. -/
def subframeBoundaryRefinementMap : (jU ⁻¹ᵁ U).toScheme ⟶ (jV ⁻¹ᵁ V).toScheme :=
  (l).resLE (jV ⁻¹ᵁ V) (jU ⁻¹ᵁ U)
    (subframeBoundaryRefinement_le e o o' ι i z r s hr hs U V hUV)

/-- Subframe chart refinement commutes with the actual boundary inclusions. -/
@[reassoc] theorem subframeBoundaryRefinement_square :
    subframeBoundaryRefinementMap e o o' ι i z r s hr hs U V hUV ≫ ((jV) ∣_ V) =
      ((jU) ∣_ U) ≫ subframeRefinementMap e o o' ι U V hUV := by
  apply (cancel_mono V.ι).mp
  simp only [subframeBoundaryRefinementMap, Category.assoc, morphismRestrict_ι,
    subframeRefinementMap_inclusion, Scheme.Hom.resLE_comp_ι_assoc,
    subframeBoundaryMap_inclusion, morphismRestrict_ι_assoc]

variable (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
  (hU : (inclusion (p := p) (q := q) I o i ⁻¹ᵁ U) ≤
    endpoint (p := p) (q := q) I o i ⁻¹ᵁ E)
  (hV : (inclusion (p := p) (q := q) J o' i ⁻¹ᵁ V) ≤
    endpoint (p := p) (q := q) J o' i ⁻¹ᵁ E)

/-- Subframe pullback retains the original open boundary coefficient exactly. -/
theorem subframeBoundaryRefinement_coefficient (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t) :
    (subframeBoundaryRefinementMap e o o' ι i z r s hr hs U V hUV).appTop
      (((endpoint J o' i).resLE E (jV ⁻¹ᵁ V) hV).appTop t) =
        ((endpoint I o i).resLE E (jU ⁻¹ᵁ U) hU).appTop t :=
  subframeChart_coefficient e o o' ι i z r s hr hs E hE (jU ⁻¹ᵁ U) (jV ⁻¹ᵁ V)
    (subframeBoundaryRefinement_le e o o' ι i z r s hr hs U V hUV) hV hU t ht

include hr hs in
/-- An exact boundary lift pulls back along strict subframes on their actual chart domains. -/
theorem subframeBoundaryRefinement_lift (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (v : Γ(V.toScheme, ⊤))
    (hv : ((jV) ∣_ V).appTop v = ((endpoint J o' i).resLE E (jV ⁻¹ᵁ V) hV).appTop t) :
    ((jU) ∣_ U).appTop ((subframeRefinementMap e o o' ι U V hUV).appTop v) =
      ((endpoint I o i).resLE E (jU ⁻¹ᵁ U) hU).appTop t := by
  calc
    _ = (subframeBoundaryRefinementMap e o o' ι i z r s hr hs U V hUV).appTop
        (((jV) ∣_ V).appTop v) := by
      change ((subframeRefinementMap e o o' ι U V hUV).appTop ≫ ((jU) ∣_ U).appTop) v =
        (((jV) ∣_ V).appTop ≫
          (subframeBoundaryRefinementMap e o o' ι i z r s hr hs U V hUV).appTop) v
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        subframeBoundaryRefinement_square]
    _ = _ := by
      rw [hv]
      exact subframeBoundaryRefinement_coefficient e o o' ι i z r s hr hs U V hUV
        E hE hU hV t ht

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
