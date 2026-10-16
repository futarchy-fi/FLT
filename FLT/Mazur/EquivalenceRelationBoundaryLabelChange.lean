/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationLabelOpenCharts
public import FLT.Mazur.EquivalenceRelationBoundaryActionGeometry

/-!
# Distinguished-label transport on the exact original boundary

The original Cartesian boundary relation lifts each label transition. The
result is an equivariant scheme isomorphism of the pulled-back boundaries,
retaining their ideals and nilpotents as well as the original closed arrows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)

/-- The label arrow lifts to the entire original boundary relation. -/
def labelTransition : boundary (p := p) (q := q) I o i ⟶ C :=
  hr.lift (inclusion I o i ≫ coordinate p q I o o') (endpoint I o i) (by
    rw [Category.assoc, coordinate_first, endpoint_condition])

omit [Mono i] in
/-- The closed label transition retains its unchanged original ambient arrow. -/
@[reassoc] theorem labelTransition_arrow :
    labelTransition (q := q) I o o' i z r hr ≫ z =
      inclusion I o i ≫ coordinate p q I o o' := hr.lift_fst _ _ _

omit [Mono i] in
/-- The closed label arrow starts at the original boundary endpoint. -/
@[reassoc] theorem labelTransition_first :
    labelTransition (q := q) I o o' i z r hr ≫ r = endpoint I o i := hr.lift_snd _ _ _

/-- The label isomorphism lifts to the full scheme-theoretic boundary. -/
def labelMap : boundary (p := p) (q := q) I o i ⟶ boundary (p := p) (q := q) I o' i :=
  pullback.lift (inclusion I o i ≫ labelChange e I o o')
    (labelTransition (q := q) I o o' i z r hr ≫ s) (by
      simp only [Category.assoc, labelChange_first]
      rw [← hs, labelTransition_arrow_assoc])

omit [Mono i] in
/-- Boundary label transport retains the entire ambient normalized frame map. -/
@[reassoc] theorem labelMap_inclusion :
    labelMap e I o o' i z r s hr hs ≫ inclusion I o' i =
      inclusion I o i ≫ labelChange e I o o' := pullback.lift_fst _ _ _

omit [Mono i] in
/-- The closed first endpoint moves by the actual closed label arrow. -/
@[reassoc] theorem labelMap_endpoint :
    labelMap e I o o' i z r s hr hs ≫ endpoint I o' i =
      labelTransition (q := q) I o o' i z r hr ≫ s := pullback.lift_snd _ _ _

/-- Successive boundary label changes agree exactly with the direct change. -/
theorem labelMap_comp (o'' : I) :
    labelMap e I o o' i z r s hr hs ≫ labelMap e I o' o'' i z r s hr hs =
      labelMap e I o o'' i z r s hr hs := by
  apply (cancel_mono (inclusion (p := p) (q := q) I o'' i)).mp
  simp only [Category.assoc, labelMap_inclusion, labelMap_inclusion_assoc, labelChange_comp]

/-- The identity label change is the identity on the complete closed scheme. -/
theorem labelMap_self : labelMap e I o o i z r s hr hs = 𝟙 _ := by
  apply (cancel_mono (inclusion (p := p) (q := q) I o i)).mp
  rw [labelMap_inclusion, labelChange_self, Category.comp_id, Category.id_comp]

/-- Distinguished-label transport is an isomorphism of the exact pulled-back boundaries. -/
def labelBoundaryIso : boundary (p := p) (q := q) I o i ≅ boundary (p := p) (q := q) I o' i where
  hom := labelMap e I o o' i z r s hr hs
  inv := labelMap e I o' o i z r s hr hs
  hom_inv_id := by rw [labelMap_comp, labelMap_self]
  inv_hom_id := by rw [labelMap_comp, labelMap_self]

/-- The entire closed boundary is Cartesian over the ambient label isomorphism. -/
theorem labelMap_isPullback :
    IsPullback (labelMap e I o o' i z r s hr hs) (inclusion I o i)
      (inclusion I o' i) (labelChange e I o o') := by
  let _ : IsIso (labelMap e I o o' i z r s hr hs) :=
    (labelBoundaryIso e I o o' i z r s hr hs).isIso_hom
  exact IsPullback.of_horiz_isIso ⟨labelMap_inclusion e I o o' i z r s hr hs⟩

/-- The moving finite-group actions commute with exact boundary label transport. -/
@[reassoc] theorem labelMap_action (σ : Equiv.Perm I) :
    labelMap e I o o' i z r s hr hs ≫ (action e I o' i z r s hr hs σ).hom =
      (action e I o i z r s hr hs σ).hom ≫ labelMap e I o o' i z r s hr hs := by
  apply (cancel_mono (inclusion (p := p) (q := q) I o' i)).mp
  simp only [Category.assoc, action_inclusion, labelMap_inclusion,
    action_inclusion_assoc, labelMap_inclusion_assoc]
  rw [labelChange_action]

omit [Mono i] in
/-- Every original equalized closed coefficient is preserved across distinguished labels. -/
@[reassoc] theorem labelMap_coefficients {S : Scheme.{0}} (c : B ⟶ S)
    (hc : r ≫ c = s ≫ c) :
    labelMap e I o o' i z r s hr hs ≫ endpoint I o' i ≫ c = endpoint I o i ≫ c := by
  rw [← Category.assoc, labelMap_endpoint, Category.assoc, ← hc,
    ← Category.assoc, labelTransition_first]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
