/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeEtale
public import FLT.Mazur.EquivalenceRelationSubframeOpenCharts
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The common open image of all strict selections

All selections from a stable source chart have the same image. Etaleness makes
this an actual open of the smaller frame scheme, and it is stable under every
target relabeling. These statements concern the whole source chart, without
replacing it by complete tests or by its reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)

include hU in
/-- Stable source charts have the same image under any two label selections. -/
theorem subframeMap_image_eq (ι κ : J ↪ I) :
    subframeMap e o o' ι '' (U : Set _) = subframeMap e o o' κ '' (U : Set _) := by
  suffices hs : ∀ ι κ : J ↪ I,
      subframeMap e o o' κ '' (U : Set _) ⊆ subframeMap e o o' ι '' (U : Set _) from
    Set.Subset.antisymm (hs κ ι) (hs ι κ)
  intro ι κ y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ι κ ι.injective κ.injective
  have hk : ι.trans σ.toEmbedding = κ := by
    ext j
    exact hσ j
  have he := subframeMap_action_source e o o' ι σ.symm
  simp only [Equiv.symm_symm, hk] at he
  refine ⟨(action e I o σ.symm).hom x, ?_, congrArg (fun g ↦ g x) he⟩
  change x ∈ (action e I o σ.symm).hom ⁻¹ᵁ U
  rwa [hU]

variable [Etale p]

/-- The actual open image of the source under a selected strict subframe. -/
def subframeImageOpen (ι : J ↪ I) : (source p q J o').Opens := by
  let _ := subframeMap_etale e o o' ι
  exact ⟨subframeMap e o o' ι '' (U : Set _),
    (subframeMap e o o' ι).isOpenMap _ U.isOpen⟩

/-- Membership is witnessed by an actual point of the unchanged source chart. -/
theorem mem_subframeImageOpen (ι : J ↪ I) (y : source p q J o') :
    y ∈ subframeImageOpen e o o' U ι ↔ ∃ x ∈ U, subframeMap e o o' ι x = y := Iff.rfl

include hU in
/-- Changing the selection does not change the image open. -/
theorem subframeImageOpen_eq (ι κ : J ↪ I) :
    subframeImageOpen e o o' U ι = subframeImageOpen e o o' U κ :=
  SetLike.coe_injective (subframeMap_image_eq e o o' U hU ι κ)

include hU in
/-- The target action preserves the actual common selection image. -/
theorem subframeImageOpen_action_mem (ι : J ↪ I) (σ : Equiv.Perm J)
    (y : source p q J o') (hy : y ∈ subframeImageOpen e o o' U ι) :
    (action e J o' σ).hom y ∈ subframeImageOpen e o o' U ι := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [subframeImageOpen_eq e o o' U hU ι (σ.symm.toEmbedding.trans ι)]
  refine ⟨x, hx, ?_⟩
  exact (congrArg (fun g ↦ g x) (subframeMap_action_target e o o' ι σ)).symm

include hU in
/-- The common image is a stable open for the full smaller-frame action. -/
theorem subframeImageOpen_stable (ι : J ↪ I) (σ : Equiv.Perm J) :
    (action e J o' σ).hom ⁻¹ᵁ subframeImageOpen e o o' U ι =
      subframeImageOpen e o o' U ι := by
  apply SetLike.ext
  intro y
  constructor
  · intro hy
    have ht := subframeImageOpen_action_mem e o o' U hU ι σ⁻¹ _ hy
    rw [map_inv] at ht
    change (action e J o' σ).inv ((action e J o' σ).hom y) ∈ _ at ht
    have he := congrArg (fun g ↦ g y) (action e J o' σ).hom_inv_id
    change (action e J o' σ).inv ((action e J o' σ).hom y) = y at he
    rwa [he] at ht
  · exact subframeImageOpen_action_mem e o o' U hU ι σ y

end FLT.Mazur.EquivalenceRelationNormalizedFrames
