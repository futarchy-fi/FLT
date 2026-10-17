/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainInteriorCharts

/-!
# Original Laurent edges of the collapsed chain

Every omitted component retains its entire Laurent open. Its two affine
presentations agree by the original projective-line gluing equation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainLaurentEdges
open PolygonCyclicAtlas PolygonCollapsedChainModel
open PolygonCollapsedChainBoundaryCharts PolygonCollapsedChainInteriorCharts
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

/-- The entire Laurent open of an omitted original component. -/
def edge {j : Fin n} (hj : j ≠ i) : ProjectiveLine.overlap K ⟶ chain K n h i :=
  ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ component K n h i hj

@[reassoc] theorem edge_ι {j : Fin n} (hj : j ≠ i) :
    edge K n h i hj ≫ (chainIdeal K n h i).subschemeι =
      PolygonNodeBranches.left K ≫ chart K n h j := by
  rw [edge, Category.assoc, Category.assoc, component_ι,
    left_componentMap, overlap_firstBranch_assoc]

/-- The other original projective chart gives precisely the same Laurent map. -/
theorem edge_eq_right {j : Fin n} (hj : j ≠ i) : edge K n h i hj =
    ProjectiveLine.overlapRight K ≫ ProjectiveLine.right K ≫ component K n h i hj := by
  rw [edge, ← Category.assoc, ProjectiveLine.overlap_condition, Category.assoc]

/-- The left puncture of an interior node is the full edge of its first component. -/
@[reassoc] theorem left_interior (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    PolygonNodeBranches.left K ≫ interior K n h i j hj hs = edge K n h i hj := by
  rw [← overlap_firstBranch, Category.assoc, first_interior]
  rfl

/-- These Laurent maps are open immersions into the whole chain. -/
instance edge_isOpenImmersion {j : Fin n} (hj : j ≠ i) :
    IsOpenImmersion (edge K n h i hj) := by
  by_cases hs : finRotate n j = i
  · have he : j = (finRotate n).symm i := (finRotate n).injective (by
      rw [hs, Equiv.apply_symm_apply])
    subst j
    change IsOpenImmersion
      (ProjectiveLine.overlapLeft K ≫ predecessorBoundary K n h i)
    infer_instance
  · rw [← left_interior K n h i j hj hs]
    infer_instance

/-- The inverted right puncture is the full edge of the successor component. -/
@[reassoc] theorem right_interior (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    (ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K ≫
      interior K n h i j hj hs = edge K n h i hs := by
  rw [← overlap_secondBranch, Category.assoc, second_interior,
    ← Category.assoc, ← ProjectiveLine.overlapRight, ← edge_eq_right]

/-- The surviving puncture of the retained boundary keeps the successor Laurent edge. -/
@[reassoc] theorem retained_puncture :
    ProjectiveLine.overlapRight K ≫ retainedBoundary K n h i =
      edge K n h i (PolygonCyclicNormalizationPullback.successor_ne n h i).symm := by
  rw [edge_eq_right]
  rfl

/-- The surviving puncture of the predecessor boundary keeps its full Laurent edge. -/
@[reassoc] theorem predecessor_puncture :
    ProjectiveLine.overlapLeft K ≫ predecessorBoundary K n h i =
      edge K n h i (prev_ne h i) := rfl

end FLT.Mazur.PolygonCollapsedChainLaurentEdges
