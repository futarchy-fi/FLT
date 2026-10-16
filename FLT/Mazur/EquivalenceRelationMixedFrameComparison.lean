/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedFrameLabelChange
public import FLT.Mazur.EquivalenceRelationCompleteSourceComparison

/-!
# Exhaustive comparison on complete tests with independent distinguished labels

The open permutation comparison now has independently labeled endpoints.
Every test supported on complete first frames factors uniquely, including
nonreduced tests. Completeness throughout an open source is still a hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)

instance retarget_isIso : IsIso (retarget e I I o o o') :=
  (retargetIso e I I o o o').isIso_hom

/-- The permutation comparison with an independently distinguished target frame. -/
def comparison : permutationRelation (p := p) (q := q) I o ⟶ relation p q I I o o' :=
  relationComparison e I o ≫ retarget e I I o o o'

instance comparison_isOpenImmersion : IsOpenImmersion (comparison e I o o') := by
  let _ := relationComparison_isOpenImmersion e I o
  exact inferInstanceAs (IsOpenImmersion (relationComparison e I o ≫ retarget e I I o o o'))

omit [Etale p] in
/-- The comparison retains the first frame on each permutation component. -/
@[reassoc] theorem component_comparison_fst (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ ≫
      comparison e I o o' ≫ fst p q I I o o' = 𝟙 _ := by
  rw [comparison, Category.assoc, retarget_fst]
  exact component_relationComparison_first e I o σ

omit [Etale p] in
/-- The second frame is the actual moving action followed by the canonical label change. -/
@[reassoc] theorem component_comparison_snd (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ ≫
      comparison e I o o' ≫ snd p q I I o o' =
        (action e I o σ).hom ≫ labelChange e I o o' := by
  simp only [comparison, Category.assoc, retarget_snd]
  exact (component_relationComparison_second_assoc e I o σ _)

omit [Etale p] in
/-- Each comparison component keeps the original arrow to its new distinguished endpoint. -/
@[reassoc] theorem component_comparison_arrow (σ : Equiv.Perm I) :
    Sigma.ι (fun _ : Equiv.Perm I ↦ source p q I o) σ ≫
      comparison e I o o' ≫ arrow p q I I o o' = coordinate p q I o (σ.symm o') := by
  apply e.right_cancellation
  · simp only [Category.assoc, arrow_first, component_comparison_fst_assoc,
      coordinate_first]
  · simp only [Category.assoc, arrow_second, component_comparison_snd_assoc,
      labelChange_first]
    exact actionMap_second e I o σ o'

variable {T : Scheme.{0}} (z : T ⟶ relation p q I I o o')
  (hz : Set.range (z ≫ fst p q I I o o') ⊆ completePointLocus (p := p) (q := q) I o)

include hz in
omit [Etale p] in
/-- Changing the target label leaves complete first support unchanged. -/
theorem retarget_complete_support :
    Set.range ((z ≫ retarget e I I o o' o) ≫ relationFirst p q I o) ⊆
      completePointLocus (p := p) (q := q) I o := by
  change Set.range ((z ≫ retarget e I I o o' o) ≫ fst p q I I o o) ⊆ _
  rwa [Category.assoc, retarget_fst]

/-- The unique scheme lift of a complete-supported mixed-label original relation test. -/
def completeLift : T ⟶ permutationRelation (p := p) (q := q) I o :=
  completeSourceLift e I o (z ≫ retarget e I I o o' o)
    (retarget_complete_support e I o o' z hz)

/-- No original mixed-label arrow is discarded by the complete-supported lift. -/
@[reassoc] theorem completeLift_comparison :
    completeLift e I o o' z hz ≫ comparison e I o o' = z := by
  rw [comparison, ← Category.assoc, completeLift, completeSourceLift_comparison]
  rw [Category.assoc, retarget_comp, retarget_self, Category.comp_id]

/-- The entire mixed-label scheme lift is unique, including on nonreduced tests. -/
theorem completeLift_unique (w : T ⟶ permutationRelation (p := p) (q := q) I o)
    (hw : w ≫ comparison e I o o' = z) : w = completeLift e I o o' z hz := by
  apply (cancel_mono (comparison e I o o')).mp
  exact hw.trans (completeLift_comparison e I o o' z hz).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
