/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainOpenCover
public import FLT.Mazur.PolygonCollapsedChainLaurentEdges

/-!
# Cartesian incidence of the full chain atlas

Index the boundary and interior charts uniformly over the original polygon.
The actual full Laurent edges lift canonically to any incident chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainCartesianAtlas
open PolygonCyclicAtlas PolygonCollapsedChainModel PolygonCollapsedChainOpenCover
open PolygonCollapsedChainBoundaryCharts PolygonCollapsedChainInteriorCharts
open PolygonCollapsedChainLaurentEdges
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

/-- The original node indexing each boundary or interior chain chart. -/
def nodeIndex : ChartIndex n i → Fin n
  | .inl false => i
  | .inl true => (finRotate n).symm i
  | .inr j => j.val

/-- The complete surviving branch, or the identity of an unchanged interior node. -/
def nodeInclusion : (a : ChartIndex n i) → chartScheme K n i a ⟶ PolygonNodeBranches.node K
  | .inl false => secondBranch K
  | .inl true => firstBranch K
  | .inr _ => 𝟙 _

/-- Every chart square is Cartesian, with the full scheme structure retained. -/
theorem isPullback (a : ChartIndex n i) :
    IsPullback (nodeInclusion K n i a) (chartMap K n h i a)
      (chart K n h (nodeIndex n i a)) (chainIdeal K n h i).subschemeι := by
  rcases a with b | j
  · cases b
    · exact retained_isPullback K n h i
    · exact predecessor_isPullback K n h i
  · exact interior_isPullback K n h i j.val j.property.1 j.property.2

@[reassoc] theorem chartMap_ι (a : ChartIndex n i) :
    chartMap K n h i a ≫ (chainIdeal K n h i).subschemeι =
      nodeInclusion K n i a ≫ chart K n h (nodeIndex n i a) :=
  (isPullback K n h i a).w.symm

include h in
/-- Each original node occurs exactly once in the full chain atlas. -/
theorem nodeIndex_injective : Function.Injective (nodeIndex n i) := by
  intro a b he
  rcases a with a | a <;> rcases b with b | b
  · cases a <;> cases b
    · rfl
    · exact ((prev_ne h i) he.symm).elim
    · exact ((prev_ne h i) he).elim
    · rfl
  · cases a
    · exact (b.property.1 he.symm).elim
    · exact (b.property.2 (by
        change (finRotate n).symm i = b.val at he
        rw [← he]
        exact Equiv.apply_symm_apply _ _)).elim
  · cases b
    · exact (a.property.1 he).elim
    · exact (a.property.2 (by
        change a.val = (finRotate n).symm i at he
        rw [he]
        exact Equiv.apply_symm_apply _ _)).elim
  · exact congrArg Sum.inr (Subtype.ext he)

/-- Lift an omitted Laurent edge to any chart at its first incident node. -/
def firstEdge (a : ChartIndex n i) (ha : nodeIndex n i a ≠ i) :
    ProjectiveLine.overlap K ⟶ chartScheme K n i a :=
  (isPullback K n h i a).lift (PolygonNodeBranches.left K) (edge K n h i ha)
    (edge_ι K n h i ha).symm

@[reassoc] theorem firstEdge_nodeInclusion (a : ChartIndex n i)
    (ha : nodeIndex n i a ≠ i) :
    firstEdge K n h i a ha ≫ nodeInclusion K n i a = PolygonNodeBranches.left K :=
  (isPullback K n h i a).lift_fst _ _ _

@[reassoc] theorem firstEdge_chartMap (a : ChartIndex n i) (ha : nodeIndex n i a ≠ i) :
    firstEdge K n h i a ha ≫ chartMap K n h i a = edge K n h i ha :=
  (isPullback K n h i a).lift_snd _ _ _

/-- Lift an omitted edge to its second incident node, keeping the coordinate inversion. -/
def secondEdge (a : ChartIndex n i) (j : Fin n) (hj : j ≠ i)
    (ha : (finRotate n).symm j = nodeIndex n i a) :
    ProjectiveLine.overlap K ⟶ chartScheme K n i a :=
  (isPullback K n h i a).lift
    ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K) (edge K n h i hj)
    (by rw [← ha, Category.assoc, ← overlap K n h j, edge_ι])

@[reassoc] theorem secondEdge_nodeInclusion (a : ChartIndex n i) (j : Fin n)
    (hj : j ≠ i) (ha : (finRotate n).symm j = nodeIndex n i a) :
    secondEdge K n h i a j hj ha ≫ nodeInclusion K n i a =
      (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K :=
  (isPullback K n h i a).lift_fst _ _ _

@[reassoc] theorem secondEdge_chartMap (a : ChartIndex n i) (j : Fin n)
    (hj : j ≠ i) (ha : (finRotate n).symm j = nodeIndex n i a) :
    secondEdge K n h i a j hj ha ≫ chartMap K n h i a = edge K n h i hj :=
  (isPullback K n h i a).lift_snd _ _ _

end FLT.Mazur.PolygonCollapsedChainCartesianAtlas
