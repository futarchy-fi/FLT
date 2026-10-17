/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeLocalSourceLift
public import FLT.Mazur.PolygonCompletePointCubicComplementComparison
public import FLT.Mazur.PolygonCompletePointFirstIncomingLocalEquality
public import FLT.Mazur.PolygonCompletePointFirstOutgoingLocalEquality

/-!
# First-stage local coordinate equality from the original cubic comparisons

Ordinary source and target node maps suffice. Source-node membership supplies
the marking localization, and the proved pole extraction identifies coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
variable {D : Type} [CommRing D] [IsLocalRing D]
variable (f g : ChartRing (parameter K 1) →+* D)
variable (hx : g (leftCoordinate (parameter K 1)) ∈ IsLocalRing.maximalIdeal D)
variable (hy : g (rightCoordinate (parameter K 1)) ∈ IsLocalRing.maximalIdeal D)
variable (hc : ∀ c : Ring K 1,
  f (algebraMap (Ring K 1) (ChartRing (parameter K 1)) c) =
    g (algebraMap (Ring K 1) (ChartRing (parameter K 1)) c))
local notation "t" => parameter K 1
local notation "β" => stageNodeLocalSourceLift K 1 g hx hy
local notation "E" => completePointWeierstrassCurve K n h i
local notation "a" j => PolygonInfinitesimal.chart (Ring K 1) (t) n h j
local notation "r" => originalStageToCompatibleProj K n h 1
local notation "c" => completePointToIntegralCubic K n h i
local notation "p" => Equiv.symm (finRotate n) i

include hc hx hy

/-- The actual outgoing contraction identifies outgoing coordinates in full local node rings. -/
theorem completePointFirstLocalCubic_left
    (he : Spec.map (CommRingCat.ofHom g) ≫ (a i) ≫ (r) ≫ (c) =
      Spec.map (CommRingCat.ofHom f) ≫ (a i) ≫ (r) ≫ (c)) :
    f (leftCoordinate (t)) = g (leftCoordinate (t)) := by
  have he' : Spec.map (CommRingCat.ofHom (β)) ≫
      completePointNodeToCubicChart K n h 1 i i ≫ integralCurveChart (E) 2 =
        Spec.map (CommRingCat.ofHom f) ≫ (a i) ≫ (r) ≫ (c) := by
    rw [completePointNodeToCubicChart_inclusion]
    simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      stageNodeLocalSourceLift_comp]
    exact he
  let v := completePointCubicComparisonTargetComplement K n h 1 i i f (β) he'
  have hv := completePointCubicComparisonTargetComplement_inclusion K n h 1 i i f (β) he'
  have hp := completePointCubicComparison_poles K n h 1 i i f (β) he'
  have hcoeff : ∀ z : Ring K 1, f (algebraMap (Ring K 1) (ChartRing (t)) z) =
      (β) (algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
        (algebraMap (Ring K 1) (ChartRing (t)) z)) := by
    intro z
    rw [stageNodeLocalSourceLift_algebraMap]
    exact hc z
  have hz : (β) (algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
      (leftCoordinate (t))) ∈ IsLocalRing.maximalIdeal D := by
    rwa [stageNodeLocalSourceLift_algebraMap]
  simpa only [stageNodeLocalSourceLift_algebraMap] using
    completePointFirstComplementPoles_eq_of_source_mem K n h i
      f v hv (β) hcoeff hp.1.symm hp.2.symm hz

/-- The actual predecessor contraction identifies incoming coordinates in full local node rings. -/
theorem completePointFirstLocalCubic_right
    (he : Spec.map (CommRingCat.ofHom g) ≫ (a (p)) ≫ (r) ≫ (c) =
      Spec.map (CommRingCat.ofHom f) ≫ (a (p)) ≫ (r) ≫ (c)) :
    f (rightCoordinate (t)) = g (rightCoordinate (t)) := by
  have he' : Spec.map (CommRingCat.ofHom (β)) ≫
      completePointNodeToCubicChart K n h 1 i (p) ≫ integralCurveChart (E) 2 =
        Spec.map (CommRingCat.ofHom f) ≫ (a (p)) ≫ (r) ≫ (c) := by
    rw [completePointNodeToCubicChart_inclusion]
    simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      stageNodeLocalSourceLift_comp]
    exact he
  let v := completePointCubicComparisonTargetComplement K n h 1 i (p) f (β) he'
  have hv := completePointCubicComparisonTargetComplement_inclusion K n h 1 i (p) f (β) he'
  have hp := completePointCubicComparison_poles K n h 1 i (p) f (β) he'
  have hcoeff : ∀ z : Ring K 1, f (algebraMap (Ring K 1) (ChartRing (t)) z) =
      (β) (algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
        (algebraMap (Ring K 1) (ChartRing (t)) z)) := by
    intro z
    rw [stageNodeLocalSourceLift_algebraMap]
    exact hc z
  have hz : (β) (algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
      (rightCoordinate (t))) ∈ IsLocalRing.maximalIdeal D := by
    rwa [stageNodeLocalSourceLift_algebraMap]
  simpa only [stageNodeLocalSourceLift_algebraMap] using
    completePointFirstIncomingComplementPoles_eq_of_source_mem K n h i
      f v hv (β) hcoeff hp.1.symm hp.2.symm hz

end FLT.Mazur.PolygonInfinitesimalStages
