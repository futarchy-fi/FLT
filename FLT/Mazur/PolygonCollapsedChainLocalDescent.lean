/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainOpenCover
public import FLT.Mazur.PolygonCollapsedChainLaurentEdges

/-!
# Local descent of endpoint-compatible maps on the collapsed chain

Construct maps on the full affine boundary and interior-node atlas. Their
Laurent restrictions are exactly the prescribed omitted component maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainLocalDescent
open PolygonCyclicAtlas PolygonCollapsedChainOpenCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (i : Fin n) {Y : Scheme}
  (f : (j : Fin n) → j ≠ i → (ProjectiveLine.scheme K ⟶ Y))
  (w : ∀ (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i),
    ProjectiveLine.zero K ≫ f j hj = ProjectiveLine.infinity K ≫ f (finRotate n j) hs)

include w in
/-- The input endpoint equation on the two whole affine branches of an interior node. -/
theorem node_condition (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    ProjectiveLine.chartZero K ≫ (ProjectiveLine.left K ≫ f j hj) =
      ProjectiveLine.chartZero K ≫ (ProjectiveLine.right K ≫ f (finRotate n j) hs) := by
  simpa only [ProjectiveLine.zero, ProjectiveLine.infinity, Category.assoc] using w j hj hs

/-- Arbitrary-target descent on the complete original interior node. -/
def nodeMap (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    PolygonNodeBranches.node K ⟶ Y :=
  (NodePinchingDescent.node_desc K (ProjectiveLine.left K ≫ f j hj)
    (ProjectiveLine.right K ≫ f (finRotate n j) hs) (node_condition K n i f w j hj hs)).choose

@[reassoc] theorem first_nodeMap (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    firstBranch K ≫ nodeMap K n i f w j hj hs = ProjectiveLine.left K ≫ f j hj :=
  (NodePinchingDescent.node_desc K _ _ (node_condition K n i f w j hj hs)).choose_spec.1.1

@[reassoc] theorem second_nodeMap (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    secondBranch K ≫ nodeMap K n i f w j hj hs =
      ProjectiveLine.right K ≫ f (finRotate n j) hs :=
  (NodePinchingDescent.node_desc K _ _ (node_condition K n i f w j hj hs)).choose_spec.1.2

/-- The prescribed map on the full Laurent open of an omitted component. -/
def inputEdge (j : Fin n) (hj : j ≠ i) : ProjectiveLine.overlap K ⟶ Y :=
  ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ f j hj

/-- The two full Laurent presentations agree, including their coordinate inversion. -/
theorem inputEdge_eq_right (j : Fin n) (hj : j ≠ i) : inputEdge K n i f j hj =
    ProjectiveLine.overlapRight K ≫ ProjectiveLine.right K ≫ f j hj := by
  rw [inputEdge, ← Category.assoc, ProjectiveLine.overlap_condition, Category.assoc]

@[reassoc] theorem left_nodeMap (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    PolygonNodeBranches.left K ≫ nodeMap K n i f w j hj hs = inputEdge K n i f j hj := by
  rw [← overlap_firstBranch, Category.assoc, first_nodeMap]
  rfl

@[reassoc] theorem right_nodeMap (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K ≫
      nodeMap K n i f w j hj hs = inputEdge K n i f (finRotate n j) hs := by
  rw [← overlap_secondBranch, Category.assoc, second_nodeMap,
    ← Category.assoc, ← ProjectiveLine.overlapRight, ← inputEdge_eq_right]

/-- The map on every actual boundary and whole-node chart of the chain. -/
def localMap (h : 2 ≤ n) : (a : ChartIndex n i) → chartScheme K n i a ⟶ Y
  | .inl false => ProjectiveLine.right K ≫ f (finRotate n i)
      (PolygonCyclicNormalizationPullback.successor_ne n h i).symm
  | .inl true => ProjectiveLine.left K ≫ f ((finRotate n).symm i) (prev_ne h i)
  | .inr j => nodeMap K n i f w j.val j.property.1 j.property.2

/-- Any global descent must restrict to the constructed maps on every whole chart. -/
theorem localMap_unique (h : 2 ≤ n) (d : PolygonCollapsedChainModel.chain K n h i ⟶ Y)
    (hd : ∀ (j : Fin n) (hj : j ≠ i),
      PolygonCollapsedChainModel.component K n h i hj ≫ d = f j hj)
    (a : ChartIndex n i) : chartMap K n h i a ≫ d = localMap K n i f w h a := by
  rcases a with b | j
  · cases b
    · change PolygonCollapsedChainBoundaryCharts.retainedBoundary K n h i ≫ d = _
      rw [PolygonCollapsedChainBoundaryCharts.retainedBoundary, Category.assoc, hd]
      rfl
    · change PolygonCollapsedChainBoundaryCharts.predecessorBoundary K n h i ≫ d = _
      rw [PolygonCollapsedChainBoundaryCharts.predecessorBoundary, Category.assoc, hd]
      rfl
  · change PolygonCollapsedChainInteriorCharts.interior K n h i j.val
      j.property.1 j.property.2 ≫ d = nodeMap K n i f w j.val j.property.1 j.property.2
    apply NodePinchingDescent.hom_ext K
    · rw [PolygonCollapsedChainInteriorCharts.first_interior_assoc, first_nodeMap, hd]
    · rw [PolygonCollapsedChainInteriorCharts.second_interior_assoc, second_nodeMap, hd]

end FLT.Mazur.PolygonCollapsedChainLocalDescent
