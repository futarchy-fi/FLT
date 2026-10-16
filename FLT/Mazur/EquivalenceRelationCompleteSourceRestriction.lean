/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSourceComparison
public import FLT.Mazur.EquivalenceRelationSourceRestriction

/-!
# The entire relation on sources supported on complete frames

If the first source map has complete support, the comparison over the entire
two-endpoint restriction is an isomorphism of schemes. The second source is
arbitrary and independent. The inverse retains the original arrow and all
coefficients, including nilpotents. This supplies no open neighborhood by itself.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) {I : Type} [Fintype I] {o : I}
  {U V : Scheme.{0}} (j : U ⟶ source p q I o) (k : V ⟶ source p q I o)

/-- The action comparison pulled back to the entire original source restriction. -/
def comparisonSource : Scheme := pullback (relationComparison e I o) (original j k)

/-- Forget the permutation lift, retaining both restricted endpoints and the original arrow. -/
def comparison : comparisonSource e j k ⟶ relation j k := pullback.snd _ _

instance comparison_isOpenImmersion : IsOpenImmersion (comparison e j k) := by
  let _ := relationComparison_isOpenImmersion e I o
  exact inferInstanceAs (IsOpenImmersion (pullback.snd _ _))

variable (hj : Set.range j ⊆ completePointLocus (p := p) (q := q) I o)

omit e [Etale p] in
include hj in
/-- Completeness of the first source controls the whole two-endpoint restriction. -/
theorem original_complete_support :
    Set.range (original j k ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o := by
  rw [original_first]
  rintro _ ⟨x, rfl⟩
  exact hj ⟨fst j k x, rfl⟩

/-- A scheme-level inverse on the entire original relation, with arbitrary second source. -/
def comparisonInverse : relation j k ⟶ comparisonSource e j k :=
  pullback.lift
    (completeSourceLift e I o (original j k) (original_complete_support j k hj)) (𝟙 _)
    (by rw [Category.id_comp]; exact completeSourceLift_comparison e I o _ _)

/-- No original restricted arrow is discarded. -/
@[reassoc] theorem comparisonInverse_comparison :
    comparisonInverse e j k hj ≫ comparison e j k = 𝟙 _ := pullback.lift_snd _ _ _

/-- The full source restriction agrees with the pulled-back permutation relation as schemes. -/
def comparisonIso : comparisonSource e j k ≅ relation j k where
  hom := comparison e j k
  inv := comparisonInverse e j k hj
  hom_inv_id := by
    apply (cancel_mono (comparison e j k)).mp
    rw [Category.assoc, comparisonInverse_comparison, Category.comp_id, Category.id_comp]
  inv_hom_id := comparisonInverse_comparison e j k hj

/-- The inverse keeps the unchanged original normalized relation map. -/
@[reassoc] theorem comparisonInverse_original :
    comparisonInverse e j k hj ≫
      pullback.fst (relationComparison e I o) (original j k) ≫ relationComparison e I o =
        original j k := by
  rw [pullback.condition, ← Category.assoc]
  change (comparisonInverse e j k hj ≫ comparison e j k) ≫ _ = _
  rw [comparisonInverse_comparison, Category.id_comp]

/-- The exact original coefficient map survives the inverse identification. -/
@[reassoc] theorem comparisonInverse_arrow :
    comparisonInverse e j k hj ≫
      pullback.fst (relationComparison e I o) (original j k) ≫
        relationComparison e I o ≫ relationArrow p q I o = arrow j k := by
  simpa only [Category.assoc, arrow] using
    congrArg (fun f ↦ f ≫ relationArrow p q I o) (comparisonInverse_original e j k hj)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.SourceRestriction
