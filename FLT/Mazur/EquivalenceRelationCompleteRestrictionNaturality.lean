/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSourceRestriction
public import FLT.Mazur.EquivalenceRelationSourceRefinement

/-!
# Naturality of the full original relation comparison

The scheme comparison on complete source support commutes with independent
refinements of both sources. Its inverse commutes too, as an equality of scheme
morphisms, so the original coefficient maps remain compatible on overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) {I : Type} [Fintype I] {o : I}
  {U V U' V' : Scheme.{0}}
  (j : U ⟶ source p q I o) (k : V ⟶ source p q I o)
  (j' : U' ⟶ source p q I o) (k' : V' ⟶ source p q I o)
  (a : U' ⟶ U) (b : V' ⟶ V) (ha : a ≫ j = j') (hb : b ≫ k = k')

omit e [Etale p] in
include ha in
/-- Complete first-source support survives any source refinement. -/
theorem complete_support_refine
    (hj : Set.range j ⊆ completePointLocus (p := p) (q := q) I o) :
    Set.range j' ⊆ completePointLocus (p := p) (q := q) I o := by
  rw [← ha]
  rintro _ ⟨x, rfl⟩
  exact hj ⟨a x, rfl⟩

/-- The comparison's source refines over the same unchanged permutation relation. -/
def comparisonRefine : comparisonSource e j' k' ⟶ comparisonSource e j k :=
  pullback.lift (pullback.fst (relationComparison e I o) (original j' k'))
    (comparison e j' k' ≫ refine j k j' k' a b ha hb) (by
      rw [Category.assoc, refine_original j k j' k' a b ha hb e]
      exact pullback.condition)

omit [Etale p] in
/-- Comparison maps commute with both source refinements. -/
@[reassoc] theorem comparisonRefine_comparison :
    comparisonRefine e j k j' k' a b ha hb ≫ comparison e j k =
      comparison e j' k' ≫ refine j k j' k' a b ha hb := pullback.lift_snd _ _ _

omit [Etale p] in
/-- The chosen permutation lift itself is unchanged by source refinement. -/
@[reassoc] theorem comparisonRefine_permutation :
    comparisonRefine e j k j' k' a b ha hb ≫
      pullback.fst (relationComparison e I o) (original j k) =
        pullback.fst (relationComparison e I o) (original j' k') := pullback.lift_fst _ _ _

/-- Inverse scheme identifications commute exactly with independent source refinements. -/
@[reassoc] theorem comparisonInverse_naturality
    (hj : Set.range j ⊆ completePointLocus (p := p) (q := q) I o) :
    comparisonInverse e j' k' (complete_support_refine j j' a ha hj) ≫
      comparisonRefine e j k j' k' a b ha hb =
        refine j k j' k' a b ha hb ≫ comparisonInverse e j k hj := by
  apply (cancel_mono (comparison e j k)).mp
  rw [Category.assoc, comparisonRefine_comparison, ← Category.assoc,
    comparisonInverse_comparison, Category.id_comp, Category.assoc,
    comparisonInverse_comparison, Category.comp_id]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
