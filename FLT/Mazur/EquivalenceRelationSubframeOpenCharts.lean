/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeRefinement

/-!
# Stable domains for all strict subframe selections

Intersect the inverse images of an independent smaller chart under every
embedding. This is an open stable under the entire larger permutation group.
The formula retains all selections; a point belongs only when all of them land.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

/-- A permutation of the larger frame permutes the actual subframe selections. -/
@[reassoc] theorem subframeMap_action_source (ι : J ↪ I) (σ : Equiv.Perm I) :
    (action e I o σ).hom ≫ subframeMap e o o' ι =
      subframeMap e o o' (ι.trans σ.symm.toEmbedding) := by
  apply hom_ext_second p q J o' e
  intro j
  change (actionMap e I o σ ≫ subframeMap e o o' ι) ≫ _ = _
  simp only [Category.assoc, subframeMap_second, actionMap_second,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply]

/-- Relabeling a smaller frame composes its actual selection on the smaller side. -/
@[reassoc] theorem subframeMap_action_target (ι : J ↪ I) (τ : Equiv.Perm J) :
    subframeMap e o o' ι ≫ (action e J o' τ).hom =
      subframeMap e o o' (τ.symm.toEmbedding.trans ι) := by
  apply hom_ext_second p q J o' e
  intro j
  change (subframeMap e o o' ι ≫ actionMap e J o' τ) ≫ _ = _
  simp only [Category.assoc, subframeMap_second, actionMap_second,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply]

/-- Every subframe preserves inverse images of original relation-invariant domains. -/
theorem subframe_preimage_domain (ι : J ↪ I) (E : A.Opens)
    (hE : p ⁻¹ᵁ E = q ⁻¹ᵁ E) :
    subframeMap e o o' ι ⁻¹ᵁ (first p q J o' ⁻¹ᵁ E) = first p q I o ⁻¹ᵁ E := by
  rw [← Scheme.Hom.comp_preimage, subframeMap_first, Scheme.Hom.comp_preimage, ← hE,
    ← Scheme.Hom.comp_preimage, coordinate_first]

/-- The actual open where every embedding lands in a given smaller chart. -/
def allSubframeOpen (V : (source p q J o').Opens) : (source p q I o).Opens :=
  ⨅ ι : J ↪ I, subframeMap e o o' ι ⁻¹ᵁ V

/-- Membership retains every strict selection, without a completeness assumption. -/
theorem mem_allSubframeOpen (V : (source p q J o').Opens) (x : source p q I o) :
    x ∈ allSubframeOpen e o o' V ↔ ∀ ι : J ↪ I, subframeMap e o o' ι x ∈ V := by
  change x ∈ ((allSubframeOpen e o o' V) : Set _) ↔ _
  rw [allSubframeOpen, TopologicalSpace.Opens.coe_iInf]
  simp only [Set.mem_iInter, SetLike.mem_coe, Scheme.Hom.mem_preimage]

/-- The full selection domain is stable under all larger-frame permutations. -/
theorem allSubframeOpen_stable (V : (source p q J o').Opens) (σ : Equiv.Perm I) :
    (action e I o σ).hom ⁻¹ᵁ allSubframeOpen e o o' V = allSubframeOpen e o o' V := by
  apply SetLike.ext
  intro x
  change (action e I o σ).hom x ∈ allSubframeOpen e o o' V ↔ _
  rw [mem_allSubframeOpen, mem_allSubframeOpen]
  have he (ι : J ↪ I) : subframeMap e o o' ι ((action e I o σ).hom x) =
      subframeMap e o o' (ι.trans σ.symm.toEmbedding) x :=
    congrArg (fun f ↦ f x) (subframeMap_action_source e o o' ι σ)
  constructor
  · intro hx ι
    have hi : (ι.trans σ.toEmbedding).trans σ.symm.toEmbedding = ι := by
      ext j
      exact σ.symm_apply_apply (ι j)
    have h := hx (ι.trans σ.toEmbedding)
    rwa [he, hi] at h
  · intro hx ι
    rw [he]
    exact hx _

/-- Each individual selection is an actual refinement on this stable domain. -/
theorem allSubframeOpen_le (V : (source p q J o').Opens) (ι : J ↪ I) :
    allSubframeOpen e o o' V ≤ subframeMap e o o' ι ⁻¹ᵁ V := iInf_le _ ι

end FLT.Mazur.EquivalenceRelationNormalizedFrames
