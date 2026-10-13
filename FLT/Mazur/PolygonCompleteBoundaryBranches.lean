/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryNormalization
public import FLT.Mazur.PolygonCompleteBoundaryNode
public import FLT.Mazur.PolygonNormalizationNodeBaseChange

/-!
# Both original branches recover the complete node frame

The zero and adjacent infinity branches give the same original node map into
the complete smoothing. Their positive-line triangles agree in all tensor degrees.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction PolygonPinching
  PolygonMarkingBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
  PolygonCyclicAtlas.polygon PolygonCyclicAtlas.normalization PolygonCyclicAtlas.nodes
  tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

variable (i j : Fin n) (s : point K ⟶ component K)

/-- The original branch incidence is retained inside the complete smoothing. -/
@[reassoc] theorem completeBoundaryNormalizationMap_node
    (w : s ≫ (componentι K n i ≫ p) = nodeι K n j ≫ q) :
    ((Over.pullback g).map s).left ≫ completeBoundaryNormalizationMap K n h g i =
      completeBoundaryNodeMap K n h g j := by
  have hw := congrArg (fun t : point K ⟶ C ↦ ((Over.pullback g).map t).left ≫
    completeBoundaryParameterMap K n h g) w
  simpa only [Functor.map_comp, Over.comp_left, Category.assoc,
    completeBoundaryNormalizationMap, completeBoundaryNodeMap] using hw

/-- Either original normalization branch recovers the exact complete node frame. -/
theorem completeBoundaryNormalizationLineIso_node
    (w : s ≫ (componentι K n i ≫ p) = nodeι K n j ≫ q) :
    LinePullbackTriangle ((Over.pullback g).map s).left
      (completeBoundaryNormalizationMap K n h g i) (completeBoundaryNodeMap K n h g j)
      (completeBoundaryNormalizationMap_node K n h g i j s w)
      (completeBoundaryNormalizationLineIso K n h g i)
      (normalizationEndpointLineIso K n hn p q hp g 1 i i j s w)
      (completeBoundaryNodeLineIso K n h g j) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeBoundaryNormalizationLineIso_section K n h g i)
    (normalizationEndpointLineIso_section K n hn p q hp g 1 i i j s w)
    (completeBoundaryNodeLineIso_section K n h g j)

variable (d : ℕ)

/-- The zero branch retains the complete family's node frame in every tensor degree. -/
theorem completeBoundaryNormalizationLineIso_zero_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.zeroSection K)).left
      (completeBoundaryNormalizationMap K n h g i) (completeBoundaryNodeMap K n h g i)
      (completeBoundaryNormalizationMap_node K n h g i i (ProjectiveLine.zeroSection K)
        (PolygonNodeIncidence.zero_node K n hn p q hp i))
      (tensorPowerPullbackComparison _ (completeBoundaryNormalizationLineIso K n h g i) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q hp g 1 i i i (ProjectiveLine.zeroSection K)
          (PolygonNodeIncidence.zero_node K n hn p q hp i)) d)
      (tensorPowerPullbackComparison _ (completeBoundaryNodeLineIso K n h g i) d) :=
  (completeBoundaryNormalizationLineIso_node K n h g i i (ProjectiveLine.zeroSection K)
    (PolygonNodeIncidence.zero_node K n hn p q hp i)).tensorPower d

/-- The adjacent infinity branch retains exactly the same complete-family node frame. -/
theorem completeBoundaryNormalizationLineIso_infinity_node :
    LinePullbackTriangle ((Over.pullback g).map (ProjectiveLine.infinitySection K)).left
      (completeBoundaryNormalizationMap K n h g (next hn i)) (completeBoundaryNodeMap K n h g i)
      (completeBoundaryNormalizationMap_node K n h g (next hn i) i
        (ProjectiveLine.infinitySection K) (PolygonNodeIncidence.infinity_node K n hn p q hp i))
      (tensorPowerPullbackComparison _
        (completeBoundaryNormalizationLineIso K n h g (next hn i)) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q hp g 1 (next hn i) (next hn i) i
          (ProjectiveLine.infinitySection K)
          (PolygonNodeIncidence.infinity_node K n hn p q hp i)) d)
      (tensorPowerPullbackComparison _ (completeBoundaryNodeLineIso K n h g i) d) :=
  (completeBoundaryNormalizationLineIso_node K n h g (next hn i) i
    (ProjectiveLine.infinitySection K)
    (PolygonNodeIncidence.infinity_node K n hn p q hp i)).tensorPower d

end FLT.Mazur.PolygonInfinitesimalStages
