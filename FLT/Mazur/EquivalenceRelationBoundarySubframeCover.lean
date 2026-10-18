/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundarySubframeGeometry
public import FLT.Mazur.EquivalenceRelationBoundarySubframeRefinement
public import FLT.Mazur.EquivalenceRelationSubframeImageCover

/-!
# Faithfully flat transport of the whole boundary along strict subframes

The independently restricted boundary square is Cartesian. Thus a surjective
selected chart map is still surjective on the whole boundary, and its boundary
pullback detects equality of sections. This includes unreduced boundaries.
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

/-- Independent open restrictions preserve the entire Cartesian boundary square. -/
theorem subframeBoundaryRefinement_isPullback :
    IsPullback b ((jU) ∣_ U) ((jV) ∣_ V) g := by
  have hP := subframeBoundaryRefinement_le e o o' ι i z r s hr hs U V hUV
  simpa only [subframeBoundaryRefinementMap, subframeRefinementMap,
    Scheme.Hom.resLE_eq_morphismRestrict] using
    Scheme.Hom.isPullback_resLE (subframeBoundaryMap_isPullback e o o' i z r s hr hs ι)
      hUV (le_rfl : jV ⁻¹ᵁ V ≤ jV ⁻¹ᵁ V) (inf_eq_right.mpr hP).symm

variable [Etale p]

/-- The boundary selection inherits etaleness by actual base change. -/
theorem subframeBoundaryRefinement_etale : Etale b := by
  let _ := subframeRefinementMap_etale e o o' ι U V hUV
  exact MorphismProperty.of_isPullback
    (subframeBoundaryRefinement_isPullback e o o' ι i z r s hr hs U V hUV).flip
    inferInstance

variable [Surjective (subframeRefinementMap e o o' ι U V hUV)]

omit [Etale p] in
/-- Surjectivity on a selected chart passes to its unreduced boundary. -/
theorem subframeBoundaryRefinement_surjective : Surjective b :=
  MorphismProperty.of_isPullback
    (subframeBoundaryRefinement_isPullback e o o' ι i z r s hr hs U V hUV).flip
    inferInstance

/-- A selected cover detects exact target boundary coefficients. -/
theorem subframeBoundaryRefinement_appTop_injective : Function.Injective (b).appTop := by
  let _ := subframeBoundaryRefinement_etale e o o' ι i z r s hr hs U V hUV
  let _ := subframeBoundaryRefinement_surjective e o o' ι i z r s hr hs U V hUV
  exact SchemeEffectiveEpiSections.appTop_injective _

variable (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
  (hU : inclusion (p := p) (q := q) I o i ⁻¹ᵁ U ≤
    endpoint (p := p) (q := q) I o i ⁻¹ᵁ E)
  (hV : inclusion (p := p) (q := q) J o' i ⁻¹ᵁ V ≤
    endpoint (p := p) (q := q) J o' i ⁻¹ᵁ E)

include hr hs in
/-- Exact lifting of an original boundary coefficient is detected on the selected cover. -/
theorem subframeBoundaryRefinement_lift_iff (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (v : Γ(V.toScheme, ⊤)) :
    ((jV) ∣_ V).appTop v = ((endpoint J o' i).resLE E (jV ⁻¹ᵁ V) hV).appTop t ↔
      ((jU) ∣_ U).appTop ((g).appTop v) =
        ((endpoint I o i).resLE E (jU ⁻¹ᵁ U) hU).appTop t := by
  constructor
  · exact subframeBoundaryRefinement_lift e o o' ι i z r s hr hs U V hUV
      E hE hU hV t ht v
  · intro hv
    apply subframeBoundaryRefinement_appTop_injective e o o' ι i z r s hr hs U V hUV
    calc
      _ = ((jU) ∣_ U).appTop ((g).appTop v) := by
        change (b ≫ ((jV) ∣_ V)).appTop v = (((jU) ∣_ U) ≫ g).appTop v
        rw [subframeBoundaryRefinement_square]
      _ = _ := hv
      _ = _ := (subframeBoundaryRefinement_coefficient e o o' ι i z r s hr hs
        U V hUV E hE hU hV t ht).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
