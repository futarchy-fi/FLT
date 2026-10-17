/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainGlobalDescent

/-!
# The component universal property of the full collapsed chain

The global glued map restricts to every prescribed complete projective line.
Thus endpoint-compatible component maps descend uniquely to arbitrary schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainComponentDescent
open PolygonCyclicAtlas PolygonCollapsedChainModel PolygonCollapsedChainOpenCover
open PolygonCollapsedChainBoundaryCharts PolygonCollapsedChainInteriorCharts
open PolygonCollapsedChainLocalDescent PolygonCollapsedChainGlobalDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n) {Y : Scheme}
  (f : (j : Fin n) → j ≠ i → (ProjectiveLine.scheme K ⟶ Y))
  (w : ∀ (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i),
    ProjectiveLine.zero K ≫ f j hj = ProjectiveLine.infinity K ≫ f (finRotate n j) hs)

/-- The descended map has the prescribed left affine restriction on every omitted component. -/
theorem left_component_desc (j : Fin n) (hj : j ≠ i) :
    ProjectiveLine.left K ≫ component K n h i hj ≫ desc K n h i f w =
      ProjectiveLine.left K ≫ f j hj := by
  by_cases hs : finRotate n j = i
  · have he : j = (finRotate n).symm i := (finRotate n).injective (by
      rw [hs, Equiv.apply_symm_apply])
    subst j
    rw [← Category.assoc]
    change predecessorBoundary K n h i ≫ desc K n h i f w = _
    exact chartMap_desc K n h i f w (.inl true)
  · rw [← first_interior_assoc K n h i j hj hs]
    have he := chartMap_desc K n h i f w (.inr ⟨j, hj, hs⟩)
    change interior K n h i j hj hs ≫ desc K n h i f w = nodeMap K n i f w j hj hs at he
    rw [he, first_nodeMap]

/-- The right affine restriction includes the retained boundary and every interior predecessor. -/
theorem right_component_desc (j : Fin n) (hj : j ≠ i) :
    ProjectiveLine.right K ≫ component K n h i hj ≫ desc K n h i f w =
      ProjectiveLine.right K ≫ f j hj := by
  by_cases hp : (finRotate n).symm j = i
  · have he : j = finRotate n i := (finRotate n).symm.injective
      (hp.trans (Equiv.symm_apply_apply _ _).symm)
    subst j
    rw [← Category.assoc]
    change retainedBoundary K n h i ≫ desc K n h i f w = _
    exact chartMap_desc K n h i f w (.inl false)
  · have hs : finRotate n ((finRotate n).symm j) ≠ i := by
      rwa [Equiv.apply_symm_apply]
    have he := chartMap_desc K n h i f w (.inr ⟨(finRotate n).symm j, hp, hs⟩)
    change interior K n h i ((finRotate n).symm j) hp hs ≫ desc K n h i f w =
      nodeMap K n i f w ((finRotate n).symm j) hp hs at he
    have hc := second_interior K n h i ((finRotate n).symm j) hp hs
    simp only [Equiv.apply_symm_apply] at hc
    rw [← Category.assoc, ← hc, Category.assoc, he, second_nodeMap]
    simp only [Equiv.apply_symm_apply]

/-- Descent recovers each prescribed complete component as a scheme morphism. -/
@[reassoc] theorem component_desc (j : Fin n) (hj : j ≠ i) :
    component K n h i hj ≫ desc K n h i f w = f j hj := by
  apply pushout.hom_ext
  · exact left_component_desc K n h i f w j hj
  · exact right_component_desc K n h i f w j hj

include w in
/-- The full closed chain is the intrinsic pinching of its omitted complete components. -/
theorem existsUnique_desc : ∃! d : chain K n h i ⟶ Y,
    ∀ (j : Fin n) (hj : j ≠ i), component K n h i hj ≫ d = f j hj := by
  refine ⟨desc K n h i f w, component_desc K n h i f w, ?_⟩
  intro e he
  exact PolygonCollapsedChainOpenCover.hom_ext K n h i e _
    (fun j hj ↦ (he j hj).trans (component_desc K n h i f w j hj).symm)

end FLT.Mazur.PolygonCollapsedChainComponentDescent
