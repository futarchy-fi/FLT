/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationLabelRefinement
public import FLT.Mazur.EquivalenceRelationBoundaryChartTransport

/-!+# Exact boundary lifts survive independently labelled refinements

The actual original closed relation constructs a map between the two entire
chart boundaries. Its square with the ambient labelled refinement commutes.
An exact lift of an original invariant open section therefore remains an exact
lift after this refinement; no global extension of that section is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o a : I)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (Z : (source p q I o).Opens) (U : (source p q I a).Opens)
  (hUZ : U ≤ labelChange e I a o ⁻¹ᵁ Z)
local notation "jZ" => inclusion (p := p) (q := q) I o i
local notation "jU" => inclusion (p := p) (q := q) I a i
local notation "l" => labelMap e I a o i z r s hr hs

include hUZ in
/-- The whole source boundary lands inside the target boundary chart. -/
theorem labelBoundaryRefinement_le : (jU ⁻¹ᵁ U) ≤ (l) ⁻¹ᵁ (jZ ⁻¹ᵁ Z) := by
  rw [← Scheme.Hom.comp_preimage, labelMap_inclusion, Scheme.Hom.comp_preimage]
  exact (jU).preimage_mono hUZ

/-- The actual map of boundary charts induced by labelled source refinement. -/
def labelBoundaryRefinementMap : (jU ⁻¹ᵁ U).toScheme ⟶ (jZ ⁻¹ᵁ Z).toScheme :=
  (l).resLE (jZ ⁻¹ᵁ Z) (jU ⁻¹ᵁ U) (labelBoundaryRefinement_le e I o a i z r s hr hs Z U hUZ)

/-- The exact boundary inclusion commutes with labelled source refinement. -/
@[reassoc] theorem labelBoundaryRefinement_square :
    labelBoundaryRefinementMap e I o a i z r s hr hs Z U hUZ ≫ ((jZ) ∣_ Z) =
      ((jU) ∣_ U) ≫ labelRefinementMap e I o Z a U hUZ := by
  apply (cancel_mono Z.ι).mp
  simp only [labelBoundaryRefinementMap, Category.assoc, morphismRestrict_ι,
    labelRefinementMap_inclusion, Scheme.Hom.resLE_comp_ι_assoc,
    labelMap_inclusion, morphismRestrict_ι_assoc]

variable (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
  (hZ : (inclusion (p := p) (q := q) I o i ⁻¹ᵁ Z) ≤ endpoint (p := p) (q := q) I o i ⁻¹ᵁ E)
  (hU : (inclusion (p := p) (q := q) I a i ⁻¹ᵁ U) ≤ endpoint (p := p) (q := q) I a i ⁻¹ᵁ E)

variable [Mono i]

/-- Label refinement retains the same original invariant open boundary coefficient. -/
theorem labelBoundaryRefinement_coefficient (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t) :
    (labelBoundaryRefinementMap e I o a i z r s hr hs Z U hUZ).appTop
      (((endpoint I o i).resLE E (jZ ⁻¹ᵁ Z) hZ).appTop t) =
        ((endpoint I a i).resLE E (jU ⁻¹ᵁ U) hU).appTop t := by
  have hQT : (jU ⁻¹ᵁ U) ≤ subframeBoundaryMap e a o i z r s hr hs
      (Function.Embedding.refl I) ⁻¹ᵁ (jZ ⁻¹ᵁ Z) := by
    rw [subframeBoundaryMap_label]
    exact labelBoundaryRefinement_le e I o a i z r s hr hs Z U hUZ
  have he := subframeChart_coefficient e a o (Function.Embedding.refl I)
    i z r s hr hs E hE (jU ⁻¹ᵁ U) (jZ ⁻¹ᵁ Z) hQT hZ hU t ht
  simpa only [subframeBoundaryMap_label, labelBoundaryRefinementMap] using he

include hr hs in
/-- An exact boundary lift on one chart stays exact on every labelled source refinement. -/
theorem labelBoundaryRefinement_lift (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (w : Γ(Z.toScheme, ⊤))
    (hw : ((jZ) ∣_ Z).appTop w = ((endpoint I o i).resLE E (jZ ⁻¹ᵁ Z) hZ).appTop t) :
    ((jU) ∣_ U).appTop ((labelRefinementMap e I o Z a U hUZ).appTop w) =
      ((endpoint I a i).resLE E (jU ⁻¹ᵁ U) hU).appTop t := by
  calc
    _ = (labelBoundaryRefinementMap e I o a i z r s hr hs Z U hUZ).appTop
        (((jZ) ∣_ Z).appTop w) := by
      change ((labelRefinementMap e I o Z a U hUZ).appTop ≫ ((jU) ∣_ U).appTop) w =
        (((jZ) ∣_ Z).appTop ≫
          (labelBoundaryRefinementMap e I o a i z r s hr hs Z U hUZ).appTop) w
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        labelBoundaryRefinement_square]
    _ = _ := by
      rw [hw]
      exact labelBoundaryRefinement_coefficient e I o a i z r s hr hs Z U hUZ
        E hE hZ hU t ht

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
