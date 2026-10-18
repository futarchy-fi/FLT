/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeOpenCharts

/-!
# The finite stable set of all selected subframes

At an actual source point, retain every smaller-frame selection. This finite
set is stable under the target permutation action, and lies in every original
invariant domain containing the source endpoint. It can therefore be placed
inside a single stable affine target using an affine envelope.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

/-- All actual smaller-frame images of the given original point. -/
def selectedSubframePoints (x : source p q I o) : Set (source p q J o') :=
  Set.range fun ι : J ↪ I ↦ subframeMap e o o' ι x

/-- There are only finitely many selected images, without a complete-frame hypothesis. -/
theorem selectedSubframePoints_finite (x : source p q I o) :
    (selectedSubframePoints e o o' x).Finite := Set.finite_range _

/-- Target relabeling preserves the entire selected-image set. -/
theorem selectedSubframePoints_stable (x : source p q I o) (σ : Equiv.Perm J) :
    (action e J o' σ).hom '' selectedSubframePoints e o o' x ⊆
      selectedSubframePoints e o o' x := by
  rintro _ ⟨_, ⟨ι, rfl⟩, rfl⟩
  refine ⟨σ.symm.toEmbedding.trans ι, ?_⟩
  exact (congrArg (fun g ↦ g x) (subframeMap_action_target e o o' ι σ)).symm

/-- Original relation-invariant domains contain all the selected endpoints at once. -/
theorem selectedSubframePoints_subset_domain (x : source p q I o) (E : A.Opens)
    (hE : p ⁻¹ᵁ E = q ⁻¹ᵁ E) (hx : first p q I o x ∈ E) :
    selectedSubframePoints e o o' x ⊆ first p q J o' ⁻¹ᵁ E := by
  rintro _ ⟨ι, rfl⟩
  change x ∈ subframeMap e o o' ι ⁻¹ᵁ (first p q J o' ⁻¹ᵁ E)
  rwa [subframe_preimage_domain e o o' ι E hE]

/-- Containing the finite selected set is exactly the all-selection neighborhood condition. -/
theorem selectedSubframePoints_subset_iff (x : source p q I o)
    (V : (source p q J o').Opens) :
    selectedSubframePoints e o o' x ⊆ V ↔ x ∈ allSubframeOpen e o o' V := by
  rw [mem_allSubframeOpen]
  exact Set.range_subset_iff

end FLT.Mazur.EquivalenceRelationNormalizedFrames
