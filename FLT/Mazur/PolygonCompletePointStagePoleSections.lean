/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStagePowerComparison
public import FLT.Mazur.PolygonCompletePointFirstOrderFactor

/-!
# The chosen complete pole sections on the original finite stages

These are transports of the particular chosen complete lifts, not newly
normalized stage sections. The homogeneous triple retains the same choices;
Y is the chosen order-three lift and Z is the canonical divisor cube.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  family originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
  completePointLineOriginalStageIso completePointPowerOriginalStageIso
  tensorPowerPullbackComparison tensorPowerIso tensorPowerCongr
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "D" => originalStageSinglePointLine K n h m i
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)

/-- The original chosen order-two lift transported to the full finite stage. -/
def completePointStagePoleTwo : Γ(tensorPower (D) 2, ⊤) :=
  completePointPowerStageSection K n h m i 2 (completePointPoleTwoSection K n h i)

/-- The original chosen order-three lift transported to the full finite stage. -/
def completePointStagePoleThree : Γ(tensorPower (D) 3, ⊤) :=
  completePointPowerStageSection K n h m i 3 (completePointProjectiveY K n h i)

/-- The actual three homogeneous sections transported through the original stage comparison. -/
def completePointStageProjectiveSections (j : Fin 3) : Γ(tensorPower (D) 3, ⊤) :=
  completePointPowerStageSection K n h m i 3 (completePointProjectiveSections K n h i j)

/-- The middle homogeneous coordinate is the same chosen order-three lift. -/
theorem completePointStageProjectiveSections_Y :
    completePointStageProjectiveSections K n h m i 1 =
      completePointStagePoleThree K n h m i := rfl

/-- The last homogeneous coordinate is the canonical cube of the original stage marking. -/
theorem completePointStageProjectiveSections_Z :
    completePointStageProjectiveSections K n h m i 2 =
      tensorPowerSection (D) ⊤ (divisorSection hI ⊤) 3 :=
  completePointPowerOriginalStageIso_section K n h m i 3

end FLT.Mazur.PolygonInfinitesimalStages
