/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStageCanonicalStep
public import FLT.Mazur.PolygonOriginalNodeMarkingComplement
public import FLT.Mazur.DivisorComplementCanonical
public import FLT.Mazur.GlobalIdealPowerCompatibility

/-!
# Actual chosen pole sections as functions near the original stage nodes

The canonical divisor frame turns the retained sections into regular functions
on the original node chart minus the marking. These opens contain the specified
coordinate nodes at every stage, including all first-stage nilpotents.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i j : Fin n)
local notation "C" => GlobalIdealPowerCompatibility.complement
  (Scheme.Hom.ker (marking K m n h i))
local notation "a" => PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)
local notation "L" => originalStageSinglePointLine K n h m i

/-- The original node-chart open on which the actual stage marking is absent. -/
def completePointStageNodeOpen : (PolygonSmoothing.chart (Ring K m) (parameter K m)).Opens :=
  (a) ⁻¹ᵁ (C)

omit [NeZero n] in
/-- This original full node-chart open contains its original coordinate node. -/
theorem completePointStageNodeOpen_mem :
    stageNodePoint K m ∈ completePointStageNodeOpen K n h m i j :=
  originalStageNode_mem_marking_complement K m n h j i

/-- A retained pole section in the canonical divisor frame on the original node-chart open. -/
def completePointStageNodeFunction (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    Γ((completePointStageNodeOpen K n h m i j).toScheme, ⊤) :=
  ((a) ∣_ (C)).appTop (divisorComplementFunction hI d s)

/-- Canonical divisor powers have local representative one in the actual node frame. -/
theorem completePointStageNodeFunction_canonical (d : ℕ) :
    completePointStageNodeFunction K n h m i j d
        (tensorPowerSection (L) ⊤ (divisorSection hI ⊤) d) = 1 := by
  unfold completePointStageNodeFunction
  erw [divisorComplementFunction_power, map_one]

/-- The particular original order-two lift, expressed in the original node frame. -/
def completePointStageNodePoleTwo :
    Γ((completePointStageNodeOpen K n h m i j).toScheme, ⊤) :=
  completePointStageNodeFunction K n h m i j 2 (completePointStagePoleTwo K n h m i)

/-- The particular original order-three lift, expressed in the original node frame. -/
def completePointStageNodePoleThree :
    Γ((completePointStageNodeOpen K n h m i j).toScheme, ⊤) :=
  completePointStageNodeFunction K n h m i j 3 (completePointStagePoleThree K n h m i)

/-- The original homogeneous coordinate sections in one canonical node-chart frame. -/
def completePointStageNodeCubic (k : Fin 3) :
    Γ((completePointStageNodeOpen K n h m i j).toScheme, ⊤) :=
  completePointStageNodeFunction K n h m i j 3
    (completePointStageProjectiveSections K n h m i k)

/-- The original local X numerator is the actual transported pole-two function. -/
theorem completePointStageNodeCubic_X :
    completePointStageNodeCubic K n h m i j 0 =
      completePointStageNodePoleTwo K n h m i j := by
  unfold completePointStageNodeCubic completePointStageNodePoleTwo
  rw [completePointStageProjectiveSections_X]
  unfold completePointStageNodeFunction
  congr 1
  exact divisorComplementFunction_cons hI 2 _

/-- The original local Y numerator is the actual transported pole-three function. -/
theorem completePointStageNodeCubic_Y :
    completePointStageNodeCubic K n h m i j 1 =
      completePointStageNodePoleThree K n h m i j := rfl

/-- The original local Z denominator is exactly one on these full node neighborhoods. -/
theorem completePointStageNodeCubic_Z :
    completePointStageNodeCubic K n h m i j 2 = 1 := by
  rw [completePointStageNodeCubic, completePointStageProjectiveSections_Z,
    completePointStageNodeFunction_canonical]

/-- All three particular coordinate functions in the same original node frame. -/
theorem completePointStageNodeCubic_coordinates (k : Fin 3) :
    completePointStageNodeCubic K n h m i j k =
      ![completePointStageNodePoleTwo K n h m i j,
        completePointStageNodePoleThree K n h m i j, 1] k := by
  fin_cases k
  · exact completePointStageNodeCubic_X K n h m i j
  · exact completePointStageNodeCubic_Y K n h m i j
  · exact completePointStageNodeCubic_Z K n h m i j

end FLT.Mazur.PolygonInfinitesimalStages
