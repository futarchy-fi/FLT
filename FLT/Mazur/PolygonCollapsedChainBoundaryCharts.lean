/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedBoundaryIdeal
public import FLT.Mazur.PolygonCollapsedChainModel

/-!
# Cartesian boundary charts of the global collapsed chain

The original affine half of each boundary component is the entire restriction
of the chain to its boundary node chart. In particular these maps are open immersions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainBoundaryCharts
open PolygonCyclicAtlas PolygonCollapsedChainModel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "I" => chainIdeal K n h i

/-- The successor's original right affine chart inside the global chain. -/
def retainedBoundary : ProjectiveLine.chart K ⟶ chain K n h i :=
  ProjectiveLine.right K ≫ component K n h i
    (PolygonCyclicNormalizationPullback.successor_ne n h i).symm

/-- The predecessor's original left affine chart inside the global chain. -/
def predecessorBoundary : ProjectiveLine.chart K ⟶ chain K n h i :=
  ProjectiveLine.left K ≫ component K n h i (prev_ne h i)

@[reassoc] theorem retainedBoundary_ι :
    retainedBoundary K n h i ≫ (I).subschemeι = secondBranch K ≫ chart K n h i := by
  rw [retainedBoundary, Category.assoc, component_ι, right_componentMap,
    Equiv.symm_apply_apply]

@[reassoc] theorem predecessorBoundary_ι :
    predecessorBoundary K n h i ≫ (I).subschemeι =
      firstBranch K ≫ chart K n h ((finRotate n).symm i) := by
  rw [predecessorBoundary, Category.assoc, component_ι, left_componentMap]

/-- The whole retained boundary chart is Cartesian over the original polygon. -/
theorem retained_isPullback : IsPullback (secondBranch K) (retainedBoundary K n h i)
    (chart K n h i) (I).subschemeι := by
  apply isPullback_of_isClosedImmersion _ _ _ _ (retainedBoundary_ι K n h i).symm
  rw [Scheme.IdealSheafData.ker_subschemeι, ← fiberIdeal_eq_chainIdeal,
    PolygonCollapsedBoundaryIdeal.retained_chart]

/-- The whole predecessor boundary chart is Cartesian over the original polygon. -/
theorem predecessor_isPullback :
    IsPullback (firstBranch K) (predecessorBoundary K n h i)
      (chart K n h ((finRotate n).symm i)) (I).subschemeι := by
  apply isPullback_of_isClosedImmersion _ _ _ _ (predecessorBoundary_ι K n h i).symm
  rw [Scheme.IdealSheafData.ker_subschemeι, ← fiberIdeal_eq_chainIdeal,
    PolygonCollapsedBoundaryIdeal.predecessor_chart]

instance retainedBoundary_isOpenImmersion : IsOpenImmersion (retainedBoundary K n h i) := by
  rw [← (retained_isPullback K n h i).isoPullback_hom_snd]
  infer_instance

instance predecessorBoundary_isOpenImmersion :
    IsOpenImmersion (predecessorBoundary K n h i) := by
  rw [← (predecessor_isPullback K n h i).isoPullback_hom_snd]
  infer_instance

end FLT.Mazur.PolygonCollapsedChainBoundaryCharts
