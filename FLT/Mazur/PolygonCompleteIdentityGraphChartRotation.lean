/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicGraphRotationLaws
public import FLT.Mazur.PolygonCompleteIdentityGraphChartLift

/-!
# Rotation between literal original graph charts

Rotating the full adic graph sends both node labels through the original
cyclic permutation. The two node coordinates themselves remain unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
  (b : ZMod n) (i j k l : Fin n) (hi : rotateIndex b i = k) (hj : rotateIndex b j = l)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => completeIdentityActionGraphAdicChartSource K n h m i j
local notation "d" => completeIdentityActionGraphAdicChartTarget K n h m i j
local notation "u" => completeIdentityActionGraphAdicChartInclusion K n h m i j
local notation "R" => completeIdentityAdicGraphRotation K n h m b

include hi in
/-- The rotated whole-graph map has its original source coordinate in the rotated node. -/
theorem completeIdentityGraphChartRotation_source_factor :
    (s) ≫ chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h k =
      ((u) ≫ (R)) ≫ completeIdentityActionGraphStageOriginalProjection K n h m := by
  rw [← hi, ← chart_rotation, ← Category.assoc,
    completeIdentityActionGraphAdicChartSource_inclusion, Category.assoc,
    Category.assoc, completeIdentityAdicGraphRotation_source]

include hj in
/-- The rotated target retains the full original target node coordinate. -/
theorem completeIdentityGraphChartRotation_target_factor :
    (d) ≫ chart (A) (t) n h l =
      ((u) ≫ (R)) ≫ completeIdentityActionGraphStageOriginalLift K n h m := by
  rw [← hj, ← chart_rotation, ← Category.assoc,
    completeIdentityActionGraphAdicChartTarget_inclusion, Category.assoc,
    Category.assoc, completeIdentityAdicGraphRotation_target]
  rfl

/-- Rotation acts between the full literal charts, without taking a new schematic image. -/
def completeIdentityGraphChartRotation :
    completeIdentityActionGraphAdicChart K n h m i j ⟶
      completeIdentityActionGraphAdicChart K n h m k l :=
  completeIdentityGraphChartLift K n h m k l ((u) ≫ (R)) (s) (d)
    (completeIdentityGraphChartRotation_source_factor K n h m b i j k hi)
    (completeIdentityGraphChartRotation_target_factor K n h m b i j l hj)

/-- The chart morphism is precisely restriction of the full original graph automorphism. -/
@[reassoc] theorem completeIdentityGraphChartRotation_inclusion :
    completeIdentityGraphChartRotation K n h m b i j k l hi hj ≫
      completeIdentityActionGraphAdicChartInclusion K n h m k l = (u) ≫ (R) :=
  completeIdentityGraphChartLift_inclusion _ _ _ _ _ _ _ _ _ _ _

/-- The full original source node coordinate is unchanged by relabeling. -/
@[reassoc] theorem completeIdentityGraphChartRotation_source :
    completeIdentityGraphChartRotation K n h m b i j k l hi hj ≫
      completeIdentityActionGraphAdicChartSource K n h m k l = (s) :=
  completeIdentityGraphChartLift_source _ _ _ _ _ _ _ _ _ _ _

/-- The full original target node coordinate is unchanged by relabeling. -/
@[reassoc] theorem completeIdentityGraphChartRotation_target :
    completeIdentityGraphChartRotation K n h m b i j k l hi hj ≫
      completeIdentityActionGraphAdicChartTarget K n h m k l = (d) :=
  completeIdentityGraphChartLift_target _ _ _ _ _ _ _ _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
