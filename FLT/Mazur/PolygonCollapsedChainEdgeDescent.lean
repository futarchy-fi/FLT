/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainCartesianAtlas
public import FLT.Mazur.PolygonCollapsedChainLocalDescent

/-!
# Descent equations on the full Laurent edges of the chain atlas

The actual Cartesian edge lifts recover the same prescribed Laurent map on
each incident chart. No reduction of the chart intersections is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainEdgeDescent
open PolygonCyclicAtlas PolygonCollapsedChainOpenCover
open PolygonCollapsedChainCartesianAtlas PolygonCollapsedChainLocalDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n) {Y : Scheme}
  (f : (j : Fin n) → j ≠ i → (ProjectiveLine.scheme K ⟶ Y))
  (w : ∀ (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i),
    ProjectiveLine.zero K ≫ f j hj = ProjectiveLine.infinity K ≫ f (finRotate n j) hs)

/-- The first Cartesian incidence restricts the chart descent to its input Laurent edge. -/
@[reassoc] theorem firstEdge_localMap (a : ChartIndex n i) (ha : nodeIndex n i a ≠ i) :
    firstEdge K n h i a ha ≫ localMap K n i f w h a =
      inputEdge K n i f (nodeIndex n i a) ha := by
  rcases a with b | j
  · cases b
    · exact (ha rfl).elim
    · have he : firstEdge K n h i (.inl true) ha = ProjectiveLine.overlapLeft K := by
        apply (cancel_mono (firstBranch K)).mp
        exact (firstEdge_nodeInclusion K n h i (.inl true) ha).trans
          (overlap_firstBranch K).symm
      rw [he]
      rfl
  · have he : firstEdge K n h i (.inr j) ha = PolygonNodeBranches.left K := by
      have he := firstEdge_nodeInclusion K n h i (.inr j) ha
      change firstEdge K n h i (.inr j) ha ≫ 𝟙 _ = _ at he
      rwa [Category.comp_id] at he
    rw [he]
    exact left_nodeMap K n i f w j.val j.property.1 j.property.2

/-- The second Cartesian incidence recovers the same full edge with its original inversion. -/
@[reassoc] theorem secondEdge_localMap (a : ChartIndex n i) (j : Fin n) (hj : j ≠ i)
    (ha : (finRotate n).symm j = nodeIndex n i a) :
    secondEdge K n h i a j hj ha ≫ localMap K n i f w h a = inputEdge K n i f j hj := by
  rcases a with b | k
  · cases b
    · have hj' : j = finRotate n i := by
        change (finRotate n).symm j = i at ha
        exact (finRotate n).symm.injective (ha.trans (Equiv.symm_apply_apply _ _).symm)
      subst j
      have he : secondEdge K n h i (.inl false) (finRotate n i) hj ha =
          ProjectiveLine.overlapRight K := by
        apply (cancel_mono (secondBranch K)).mp
        have he := secondEdge_nodeInclusion K n h i (.inl false) (finRotate n i) hj ha
        dsimp only [nodeInclusion] at he
        rw [he, ProjectiveLine.overlapRight, Category.assoc, overlap_secondBranch]
      rw [he, inputEdge_eq_right]
      rfl
    · have he : j = i := (finRotate n).symm.injective ha
      exact (hj he).elim
  · have he : secondEdge K n h i (.inr k) j hj ha =
        (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K := by
      have he := secondEdge_nodeInclusion K n h i (.inr k) j hj ha
      change secondEdge K n h i (.inr k) j hj ha ≫ 𝟙 _ = _ at he
      rwa [Category.comp_id] at he
    rw [he]
    change (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K ≫
      nodeMap K n i f w k.val k.property.1 k.property.2 = _
    rw [right_nodeMap]
    have hj' : finRotate n k.val = j := by
      change (finRotate n).symm j = k.val at ha
      rw [← ha, Equiv.apply_symm_apply]
    subst j
    rfl

end FLT.Mazur.PolygonCollapsedChainEdgeDescent
