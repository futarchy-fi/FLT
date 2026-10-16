/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryLabelChange
public import FLT.Mazur.EquivalenceRelationNormalizedSubframe

/-!
# Moving subframes on the exact original boundary

The full Cartesian closed relation lifts the original arrow of every subframe
selection. The resulting morphisms act on the actual pulled-back closed schemes,
commute with composition, and preserve every original equalized coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H] (o : I) (o' : J)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)

/-- A moving subframe lifts to the exact original closed source. -/
def subframeBoundaryMap (ι : J ↪ I) :
    boundary (p := p) (q := q) I o i ⟶ boundary (p := p) (q := q) J o' i :=
  pullback.lift (inclusion I o i ≫ subframeMap e o o' ι)
    (labelTransition (q := q) I o (ι o') i z r hr ≫ s) (by
      simp only [Category.assoc, subframeMap_first]
      rw [← hs, labelTransition_arrow_assoc])

omit [Mono i] in
/-- The boundary map retains the whole ambient subframe map. -/
@[reassoc] theorem subframeBoundaryMap_inclusion (ι : J ↪ I) :
    subframeBoundaryMap e o o' i z r s hr hs ι ≫ inclusion J o' i =
      inclusion I o i ≫ subframeMap e o o' ι := pullback.lift_fst _ _ _

omit [Mono i] in
/-- The closed endpoint moves along the actual original closed arrow. -/
@[reassoc] theorem subframeBoundaryMap_endpoint (ι : J ↪ I) :
    subframeBoundaryMap e o o' i z r s hr hs ι ≫ endpoint J o' i =
      labelTransition (q := q) I o (ι o') i z r hr ≫ s := pullback.lift_snd _ _ _

/-- Successive selections agree on the entire closed scheme, retaining nilpotents. -/
theorem subframeBoundaryMap_comp (o'' : H) (ι : J ↪ I) (κ : H ↪ J) :
    subframeBoundaryMap e o o' i z r s hr hs ι ≫
      subframeBoundaryMap e o' o'' i z r s hr hs κ =
        subframeBoundaryMap e o o'' i z r s hr hs (κ.trans ι) := by
  apply (cancel_mono (inclusion (p := p) (q := q) H o'' i)).mp
  simp only [Category.assoc, subframeBoundaryMap_inclusion,
    subframeBoundaryMap_inclusion_assoc, subframeMap_comp]

/-- Keeping every label and its distinguished point is the identity on the exact boundary. -/
theorem subframeBoundaryMap_refl :
    subframeBoundaryMap e o o i z r s hr hs (Function.Embedding.refl I) = 𝟙 _ := by
  apply (cancel_mono (inclusion (p := p) (q := q) I o i)).mp
  rw [subframeBoundaryMap_inclusion, subframeMap_refl, Category.comp_id, Category.id_comp]

/-- Canonical label transport is the full-size special case of boundary subframe selection. -/
theorem subframeBoundaryMap_label (j : I) :
    subframeBoundaryMap e o j i z r s hr hs (Function.Embedding.refl I) =
      labelMap e I o j i z r s hr hs := by
  apply (cancel_mono (inclusion (p := p) (q := q) I j i)).mp
  rw [subframeBoundaryMap_inclusion, labelMap_inclusion, subframeMap_label]

omit [Mono i] in
/-- Every original equalized closed coefficient survives arbitrary mixed-size selection. -/
@[reassoc] theorem subframeBoundaryMap_coefficients (ι : J ↪ I) {S : Scheme.{0}}
    (c : B ⟶ S) (hc : r ≫ c = s ≫ c) :
    subframeBoundaryMap e o o' i z r s hr hs ι ≫ endpoint J o' i ≫ c =
      endpoint I o i ≫ c := by
  rw [← Category.assoc, subframeBoundaryMap_endpoint, Category.assoc, ← hc,
    ← Category.assoc, labelTransition_first]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
