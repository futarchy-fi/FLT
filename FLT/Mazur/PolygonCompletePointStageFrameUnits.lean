/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStageEquationFrames
public import FLT.Mazur.PolygonCompletePointStagePoleCoefficients
public import FLT.Mazur.ModuleFrameComparisonUnit

/-!
# Exact units between the equation and retained pole frames

The equation frame and the unchanged complete pole frame are independently
specified. Their actual transition unit computes every coefficient change.
In particular the original pole lifts have unit, rather than prescribed one,
coefficients in the equation frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "L" => originalStageSinglePointLine K n h m i

/-- The actual unit from the retained complete pole frame to the specified equation frame. -/
irreducible_def completePointStageFrameUnit (d : ℕ) : Γ(Spec (.of (Ring K m)), ⊤)ˣ :=
  frameComparisonUnit (completePointStageEquationFrame K n h m i d)
    (completePointStagePoleFrame K n h m i d) ⊤

/-- Every original section changes coefficient by precisely this retained comparison unit. -/
theorem completePointStageEquationCoefficient_compare (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    completePointStageEquationCoefficient K n h m i d s =
      (completePointStageFrameUnit K n h m i d : Γ(Spec (.of (Ring K m)), ⊤)) *
        completePointStagePoleCoefficient K n h m i d s := by
  rw [completePointStageFrameUnit_def]
  exact frameComparisonUnit_apply _ _ ⊤ _

/-- The original order-two lift has its actual comparison unit in equation coordinates. -/
theorem completePointStagePoleTwo_equationCoefficient :
    completePointStageEquationCoefficient K n h m i 2 (completePointStagePoleTwo K n h m i) =
      (completePointStageFrameUnit K n h m i 2 : Γ(Spec (.of (Ring K m)), ⊤)) := by
  rw [completePointStageEquationCoefficient_compare,
    completePointStagePoleTwo_coefficient, mul_one]

/-- The original order-three lift retains its own exact equation-frame coefficient. -/
theorem completePointStagePoleThree_equationCoefficient :
    completePointStageEquationCoefficient K n h m i 3
      (completePointStagePoleThree K n h m i) =
      (completePointStageFrameUnit K n h m i 3 : Γ(Spec (.of (Ring K m)), ⊤)) := by
  rw [completePointStageEquationCoefficient_compare,
    completePointStagePoleThree_coefficient, mul_one]

/-- The actual quadratic equation coefficient is a unit over the full stage ring. -/
theorem completePointStagePoleTwo_equationCoefficient_isUnit :
    IsUnit (completePointStageEquationCoefficient K n h m i 2
      (completePointStagePoleTwo K n h m i)) := by
  rw [completePointStagePoleTwo_equationCoefficient]
  exact Units.isUnit _

/-- The actual cubic equation coefficient is a unit without reducing the stage ring. -/
theorem completePointStagePoleThree_equationCoefficient_isUnit :
    IsUnit (completePointStageEquationCoefficient K n h m i 3
      (completePointStagePoleThree K n h m i)) := by
  rw [completePointStagePoleThree_equationCoefficient]
  exact Units.isUnit _

end FLT.Mazur.PolygonInfinitesimalStages
