/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPointStalkComposition
public import FLT.Mazur.PolygonNodeNeighborhoodScalars

/-!
# Original chart stalk maps from the actual complete node

The original chart maps to the complete family induce stalk maps at the same
specified complete node. Adjacent chart restrictions commute with these maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing ClosedPointStalkMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)

/-- The original chart induces the actual complete-node-to-chart stalk map. -/
def completeNodeChartStalkMap (m : ℕ) :
    (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i) ⟶
      (Spec (.of (ChartRing (parameter K m)))).presheaf.stalk (stageNodePoint K m) :=
  pointMap (originalStageToCompatibleProj K n h m) (originalStageNode K n h m i)
    (completeNode K n h i) (originalStageNode_toComplete K n h m i) ≫
      (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
        (stageNodePoint K m)

/-- The composite description is the stalk map of the actual chart-to-complete morphism. -/
theorem completeNodeChartStalkMap_eq (m : ℕ) :
    completeNodeChartStalkMap K n h i m =
      pointMap (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i ≫
        originalStageToCompatibleProj K n h m) (stageNodePoint K m) (completeNode K n h i)
        (originalStageNode_toComplete K n h m i) :=
  pointMap_comp (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i)
    (originalStageToCompatibleProj K n h m) (stageNodePoint K m)
    (originalStageNode K n h m i) (completeNode K n h i) rfl
    (originalStageNode_toComplete K n h m i)

/-- Original adjacent chart restrictions commute with their actual maps to the complete family. -/
theorem nodeChartToComplete_transition (m : ℕ) :
    Spec.map (CommRingCat.ofHom (stageChartRestriction K m)) ≫
      (PolygonInfinitesimal.chart (Ring K (m + 1)) (parameter K (m + 1)) n h i ≫
        originalStageToCompatibleProj K n h (m + 1)) =
      PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i ≫
        originalStageToCompatibleProj K n h m := by
  rw [← Category.assoc, ← chart_stageRestriction, Category.assoc]
  congr 1
  simpa only [stageSystem, CategoryTheory.Functor.ofSequence_map_homOfLE_succ] using
    originalStageToCompatibleProj_naturality K n h (homOfLE (Nat.le_succ m))

/-- The same original adjacent chart map commutes on actual complete-node germs. -/
theorem completeNodeChartStalkMap_transition (m : ℕ) :
    completeNodeChartStalkMap K n h i (m + 1) ≫
      pointMap (Spec.map (CommRingCat.ofHom (stageChartRestriction K m)))
        (stageNodePoint K m) (stageNodePoint K (m + 1)) (stageChartRestriction_nodePoint m K) =
      completeNodeChartStalkMap K n h i m := by
  rw [completeNodeChartStalkMap_eq, pointMap_comp, completeNodeChartStalkMap_eq]
  exact pointMap_congr (nodeChartToComplete_transition K n h i m) _ _ _ _

variable (U : (exactVeroneseProj K n h).affineOpens)
  (hx : completeNode K n h i ∈ U.1)

/-- The actual complete-node stalk map retains the germ of each original section restriction. -/
theorem completeNodeChartStalkMap_germ (m : ℕ)
    (a : Γ(exactVeroneseProj K n h, U)) :
    completeNodeChartStalkMap K n h i m
      ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a) =
        (PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
          (stageNodePoint K m) ((family K m n h).left.presheaf.germ
            (originalStageToCompatibleProj K n h m ⁻¹ᵁ U) (originalStageNode K n h m i)
            (originalStageNode_mem_preimage K n h i U hx m)
            ((originalStageToCompatibleProj K n h m).app U a)) := by
  rw [completeNodeChartStalkMap, CommRingCat.comp_apply]
  have he := pointMap_germ (originalStageToCompatibleProj K n h m)
    (originalStageNode K n h m i) (completeNode K n h i)
    (originalStageNode_toComplete K n h m i) U
    (originalStageToCompatibleProj K n h m ⁻¹ᵁ U) le_rfl
    (originalStageNode_mem_preimage K n h i U hx m) hx a
  rw [Scheme.Hom.appLE_eq_app] at he
  exact congrArg ((PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h i).stalkMap
    (stageNodePoint K m)) he

/-- Localizing the actual neighborhood comparison gives the original complete-node germ. -/
theorem completeNodeChartNeighborhood_localize (m : ℕ)
    (a : Γ(exactVeroneseProj K n h, U)) :
    stageChartNodeStalkQuotient K m (m + 1)
      (completeNodeChartNeighborhood K n h i U hx m (Ideal.Quotient.mk _ a)) =
        Ideal.Quotient.mk _ (completeNodeChartStalkMap K n h i m
          ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a)) := by
  rw [completeNodeChartNeighborhood, RingEquiv.trans_apply, completeNodeNeighborhood_mk,
    originalNodeAffineChartQuotient_localize]
  exact congrArg (Ideal.Quotient.mk _) (completeNodeChartStalkMap_germ K n h i U hx m a).symm

end FLT.Mazur.PolygonInfinitesimalStages
