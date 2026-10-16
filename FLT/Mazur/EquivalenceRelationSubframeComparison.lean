/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeGraphs
public import FLT.Mazur.EquivalenceRelationCompleteSubframe
public import FLT.Mazur.EquivalenceRelationCompletePointLocus

/-!
# The finite embedding comparison covers complete first frames

The disjoint union indexed by label embeddings is an open subscheme of the full
mixed relation. Every scheme test supported on complete first frames factors
through it uniquely, with no completeness or equal-size condition on the second.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

/-- A finite disjoint union of actual source schemes indexed by all target label embeddings. -/
def embeddingRelation : Scheme := ∐ fun _ : J ↪ I ↦ source p q I o

/-- The comparison retains both independent frames and the actual original arrow. -/
def embeddingComparison : embeddingRelation (p := p) (q := q) (J := J) o ⟶
    relation p q I J o o' := Sigma.desc (subframeGraph e o o')

/-- Each component is its actual subframe graph in the full original relation. -/
@[reassoc] theorem component_embeddingComparison (ι : J ↪ I) :
    Sigma.ι (fun _ : J ↪ I ↦ source p q I o) ι ≫ embeddingComparison e o o' =
      subframeGraph e o o' ι := Sigma.ι_comp_desc _ _

variable [Etale p]

/-- The embedding relation is an open subscheme of the entire original mixed relation. -/
instance embeddingComparison_isOpenImmersion :
    IsOpenImmersion (embeddingComparison e o o') := by
  let _ := fun ι ↦ subframeGraph_isOpenImmersion e o o' ι
  exact AlgebraicGeometry.isOpenImmersion_sigmaDesc _ (subframeGraph e o o')
    (fun ι κ h ↦ subframeGraph_disjoint e o o' ι κ h)

/-- Every geometric original arrow from a complete frame occurs in the finite comparison. -/
theorem complete_factors_embeddingComparison {K : Type} [Field K]
    (z : Spec (.of K) ⟶ relation p q I J o o')
    (hz : Complete I o (z ≫ fst p q I J o o')) :
    ∃ w : Spec (.of K) ⟶ embeddingRelation (p := p) (q := q) (J := J) o,
      w ≫ embeddingComparison e o o' = z := by
  obtain ⟨ι, hι, _⟩ := complete_original_arrow_unique_embedding e o o'
    (z ≫ fst p q I J o o') (z ≫ snd p q I J o o') hz
    (z ≫ arrow p q I J o o')
    (by simp only [Category.assoc, arrow_first])
    (by simp only [Category.assoc, arrow_second])
  refine ⟨(z ≫ fst p q I J o o') ≫
    Sigma.ι (fun _ : J ↪ I ↦ source p q I o) ι, ?_⟩
  rw [Category.assoc, component_embeddingComparison]
  exact subframeGraph_factor e o o' z ι hι

variable {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')
  (hz : Set.range (z ≫ fst p q I J o o') ⊆ completePointLocus (p := p) (q := q) I o)

include hz in
/-- Complete first support suffices even when the second source has a different size. -/
theorem embedding_complete_source_range :
    Set.range z ⊆ Set.range (embeddingComparison e o o') := by
  rintro _ ⟨x, rfl⟩
  let v := T.fromSpecResidueField x ≫ z
  have hx : v default = z x := by
    change z (T.fromSpecResidueField x default) = z x
    rw [Scheme.fromSpecResidueField_apply]
  have hc : Complete I o (v ≫ fst p q I J o o') := by
    rw [complete_iff_mem_completePointLocus]
    change fst p q I J o o' (v default) ∈ _
    rw [hx]
    exact hz ⟨x, rfl⟩
  obtain ⟨w, hw⟩ := complete_factors_embeddingComparison e o o' v hc
  exact ⟨w default, (congrArg (fun f ↦ f default) hw).trans hx⟩

/-- The unique lift of an arbitrary complete-supported test, including nonreduced tests. -/
def embeddingCompleteLift : T ⟶ embeddingRelation (p := p) (q := q) (J := J) o :=
  IsOpenImmersion.lift _ z (embedding_complete_source_range e o o' z hz)

/-- The finite embedding lift retains the entire original relation morphism. -/
@[reassoc] theorem embeddingCompleteLift_comparison :
    embeddingCompleteLift e o o' z hz ≫ embeddingComparison e o o' = z :=
  IsOpenImmersion.lift_fac _ z (embedding_complete_source_range e o o' z hz)

/-- There is no choice of local embeddings left in the resulting scheme lift. -/
theorem embeddingCompleteLift_unique
    (w : T ⟶ embeddingRelation (p := p) (q := q) (J := J) o)
    (hw : w ≫ embeddingComparison e o o' = z) : w = embeddingCompleteLift e o o' z hz := by
  apply (cancel_mono (embeddingComparison e o o')).mp
  exact hw.trans (embeddingCompleteLift_comparison e o o' z hz).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
