/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonArithmeticNodeTransition
public import FLT.Mazur.PolygonOriginalAffineNeighborhood

/-!
# Specified nodes on the actual complete polygon

The (x,y) point on each original arithmetic chart gives a point of its glued
stage. The original stage maps retain these points, and all their images in
the actual complete candidate coincide. The stage stalk is the localization
of its original chart ring at that same coordinate ideal.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The chosen coordinate origin on the i-th actual glued stage chart. -/
def originalStageNode (m : ℕ) (i : Fin n) : (family K m n h).left :=
  PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i (stageNodePoint K m)

omit [NeZero n] in
/-- The actual glued restriction takes the specified node to the next specified node. -/
theorem originalStageNode_restriction (m : ℕ) (i : Fin n) :
    stageRestriction K m n h (originalStageNode K n h m i) =
      originalStageNode K n h (m + 1) i := by
  unfold originalStageNode
  change (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i ≫
    stageRestriction K m n h) (stageNodePoint K m) = _
  rw [chart_stageRestriction, Scheme.Hom.comp_apply]
  change PolygonInfinitesimal.chart _ _ n h i
    (PrimeSpectrum.comap (stageChartRestriction K m) (stageNodePoint K m)) = _
  rw [stageChartRestriction_nodePoint]

/-- The actual complete candidate's chosen node is the image of its original zero stage. -/
def completeNode (i : Fin n) : exactVeroneseProj K n h :=
  originalStageToCompatibleProj K n h 0 (originalStageNode K n h 0 i)

/-- Every original stage node maps to this same specified point of the complete candidate. -/
theorem originalStageNode_toComplete (m : ℕ) (i : Fin n) :
    originalStageToCompatibleProj K n h m (originalStageNode K n h m i) =
      completeNode K n h i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : stageRestriction K m n h ≫ originalStageToCompatibleProj K n h (m + 1) =
        originalStageToCompatibleProj K n h m := by
      simpa only [stageSystem, CategoryTheory.Functor.ofSequence_map_homOfLE_succ] using
        originalStageToCompatibleProj_naturality K n h (homOfLE (Nat.le_succ m))
    rw [← originalStageNode_restriction K n h m i, ← Scheme.Hom.comp_apply, he]
    exact ih

/-- The specified original node ideal is maximal at every stage. -/
instance originalStageNodeIdeal_maximal (m : ℕ) :
    (PolygonSmoothing.coordinateIdeal (parameter K m)).IsMaximal :=
  stageNodeIdeal_isMaximal K m

/-- The actual stage stalk is the localization at the original coordinate node ideal. -/
def originalStageNodeStalkIso (m : ℕ) (i : Fin n) :
    (family K m n h).left.presheaf.stalk (originalStageNode K n h m i) ≅
      CommRingCat.of (Localization.AtPrime (PolygonSmoothing.coordinateIdeal (parameter K m))) :=
  asIso ((PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
    (stageNodePoint K m)) ≪≫ AlgebraicGeometry.Spec.stalkIso
      (.of (PolygonSmoothing.ChartRing (parameter K m))) (stageNodePoint K m)

omit [NeZero n] in
/-- The stalk comparison is induced by the original open chart's stalk map. -/
theorem originalStageNodeStalkIso_hom (m : ℕ) (i : Fin n) :
    (originalStageNodeStalkIso K n h m i).hom =
      (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
        (stageNodePoint K m) ≫ (AlgebraicGeometry.Spec.stalkIso
      (.of (PolygonSmoothing.ChartRing (parameter K m))) (stageNodePoint K m)).hom := rfl

end FLT.Mazur.PolygonInfinitesimalStages
