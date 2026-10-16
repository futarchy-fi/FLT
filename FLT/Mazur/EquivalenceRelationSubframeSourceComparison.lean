/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeComparison

/-!
# Exact mixed-size source comparisons and refinement

Over every mixed relation test supported on complete first frames, the pulled-back
embedding comparison is an isomorphism. Its inverse retains the original arrow
and commutes with all refinements of the test, including infinitesimal tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

omit [Etale p] in
/-- Each embedding component keeps its independently chosen first source. -/
@[reassoc] theorem component_embeddingComparison_fst (ι : J ↪ I) :
    Sigma.ι (fun _ : J ↪ I ↦ source p q I o) ι ≫
      embeddingComparison e o o' ≫ fst p q I J o o' = 𝟙 _ := by
  rw [← Category.assoc, component_embeddingComparison, subframeGraph_fst]

omit [Etale p] in
/-- The smaller frame is the actual endpoint-moving subframe on each component. -/
@[reassoc] theorem component_embeddingComparison_snd (ι : J ↪ I) :
    Sigma.ι (fun _ : J ↪ I ↦ source p q I o) ι ≫
      embeddingComparison e o o' ≫ snd p q I J o o' = subframeMap e o o' ι := by
  rw [← Category.assoc, component_embeddingComparison, subframeGraph_snd]

omit [Etale p] in
/-- The original arrow, with all its coefficient maps, is retained on each component. -/
@[reassoc] theorem component_embeddingComparison_arrow (ι : J ↪ I) :
    Sigma.ι (fun _ : J ↪ I ↦ source p q I o) ι ≫
      embeddingComparison e o o' ≫ arrow p q I J o o' = coordinate p q I o (ι o') := by
  rw [← Category.assoc, component_embeddingComparison, subframeGraph_arrow]

variable {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')
  (hz : Set.range (z ≫ fst p q I J o o') ⊆ completePointLocus (p := p) (q := q) I o)

omit e [Etale p] in
include hz in
/-- Complete first support survives arbitrary independent refinement of a relation test. -/
theorem embedding_complete_source_precomp {T' : Scheme.{0}} (a : T' ⟶ T) :
    Set.range ((a ≫ z) ≫ fst p q I J o o') ⊆
      completePointLocus (p := p) (q := q) I o := by
  rintro _ ⟨x, rfl⟩
  exact hz ⟨a x, rfl⟩

/-- The whole embedding lift commutes with every scheme refinement. -/
@[reassoc] theorem embeddingCompleteLift_naturality {T' : Scheme.{0}} (a : T' ⟶ T) :
    a ≫ embeddingCompleteLift e o o' z hz =
      embeddingCompleteLift e o o' (a ≫ z)
        (embedding_complete_source_precomp o o' z hz a) := by
  apply embeddingCompleteLift_unique
  rw [Category.assoc, embeddingCompleteLift_comparison]

/-- The entire original test is canonically isomorphic to its pulled-back finite comparison. -/
def embeddingSourceIso : pullback (embeddingComparison e o o') z ≅ T where
  hom := pullback.snd _ _
  inv := pullback.lift (embeddingCompleteLift e o o' z hz) (𝟙 _) (by
    rw [Category.id_comp]; exact embeddingCompleteLift_comparison e o o' z hz)
  hom_inv_id := by
    apply (cancel_mono (pullback.snd (embeddingComparison e o o') z)).mp
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := pullback.lift_snd _ _ _

/-- The inverse finite comparison keeps the unchanged original relation test. -/
@[reassoc] theorem embeddingSourceIso_inv_original :
    (embeddingSourceIso e o o' z hz).inv ≫
      pullback.fst (embeddingComparison e o o') z ≫ embeddingComparison e o o' = z := by
  rw [← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.fst _ _) ≫ _ = _
  rw [pullback.lift_fst, embeddingCompleteLift_comparison]

/-- The inverse retains the actual original arrow on the full, possibly nonreduced test. -/
@[reassoc] theorem embeddingSourceIso_inv_arrow :
    (embeddingSourceIso e o o' z hz).inv ≫
      pullback.fst (embeddingComparison e o o') z ≫
        embeddingComparison e o o' ≫ arrow p q I J o o' = z ≫ arrow p q I J o o' := by
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ arrow p q I J o o')
    (embeddingSourceIso_inv_original e o o' z hz)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
