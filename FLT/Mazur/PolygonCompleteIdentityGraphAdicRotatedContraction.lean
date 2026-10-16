/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphRotatedContraction
public import FLT.Mazur.PolygonCompleteIdentityFiniteInputRotation
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicParameter

/-!
# Rotated contraction equations survive literal adic base change

Pull back the proved complete-graph equations along the original stage map.
The two sides retain the original finite source and target, including all
nilpotents and the unchanged universal unit parameter.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "l" => completeIdentityActionGraphStageOriginalLift K n h m
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "r" => originalStageToCompatibleProj K n h m
local notation "f" => completeIdentityFiniteInput K n h 0 m
local notation "ρ" => rotation (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h b

/-- The complete-valued stage lift retains every rotated contraction equation. -/
@[reassoc] theorem completeIdentityActionGraphStageLift_rotatedContraction :
    completeIdentityActionGraphStageLift K n h m ≫ completeRotation K n h b ≫ (g) =
      (p) ≫ (ρ) ≫ (f) ≫ (a) := by
  rw [completeIdentityActionGraphStageLift, Category.assoc,
    completeIdentityActionGraphLift_rotatedContraction,
    completeIdentityFiniteInput_rotation_assoc,
    completeIdentityActionGraphStageOriginalProjection_input_assoc]
  simp only [completeIdentityActionGraphStageInclusion,
    completeIdentityActionGraphStageProjection, pullback.condition_assoc]

/-- The equation is on the actual original stage target and source, not their images. -/
@[reassoc] theorem completeIdentityActionGraphStageOriginalLift_rotatedContraction :
    (l) ≫ stageRotation K n h m b ≫ (r) ≫ (g) =
      (p) ≫ (ρ) ≫ (f) ≫ (a) := by
  rw [← originalStageToCompatibleProj_rotation_assoc,
    completeIdentityActionGraphStageOriginalLift_realization_assoc,
    completeIdentityActionGraphStageLift_rotatedContraction]

/-- Keeping the original source unit in the target preserves the rotated equation. -/
@[reassoc] theorem completeIdentityActionGraphStageParameterizedTarget_rotatedContraction :
    completeIdentityActionGraphStageParameterizedTarget K n h m ≫ (ρ) ≫
        scalingParameterProjection (A) (t) n h ≫ (r) ≫ (g) =
      (p) ≫ (ρ) ≫ (f) ≫ (a) := by
  rw [completeIdentityFiniteProjection_rotation_assoc,
    completeIdentityActionGraphStageParameterizedTarget_projection_assoc,
    completeIdentityActionGraphStageOriginalLift_rotatedContraction]

end FLT.Mazur.PolygonInfinitesimalStages
