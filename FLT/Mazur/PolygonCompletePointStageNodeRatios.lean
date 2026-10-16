/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStageNodeFunctions
public import FLT.Mazur.PolygonCompletePointStageCubicRatios
public import FLT.Mazur.DivisorComplementSectionRatios

/-!
# The actual complete cubic ratios in the original stage node frames

The constructed node functions represent the particular original complete
cubic sections after restriction to the full stage. The canonical Z frame
is valid at every original node, without passing to a reduced branch.
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
local notation "f" => originalStageToCompatibleProj K n h m
local notation "a" => PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j
local notation "C" => GlobalIdealPowerCompatibility.complement
  (Scheme.Hom.ker (marking K m n h i))
local notation "L" => tensorPower (completePointLine K n h i) 3
local notation "M" => tensorPower (originalStageSinglePointLine K n h m i) 3
local notation "s" => completePointProjectiveSections K n h i
local notation "t" => completePointStageProjectiveSections K n h m i
local notation "O" => sectionGeneratorOpen (L) (s 2)

/-- The stage marking complement is exactly the inverse image of the complete Z chart. -/
theorem completePointStageComplement_preimage : (C) = (f) ⁻¹ᵁ (O) := by
  rw [← completePointStageProjectiveSections_generator,
    completePointStageProjectiveSections_Z_open]

/-- The actual canonical node function is the ratio of the same transported cubic sections. -/
theorem completePointStageNodeCubic_ratio (k : Fin 3) :
    completePointStageNodeCubic K n h m i j k =
      ((a) ∣_ (C)).appTop ((C).topIso.inv
        (sectionRatioOn (M) (t 2) (C)
          (completePointStageProjectiveSections_Z_open K n h m i).ge (t k))) := by
  unfold completePointStageNodeCubic completePointStageNodeFunction
  congr 1
  simp only [completePointStageProjectiveSections_Z]
  exact divisorComplementFunction_eq_ratio
    (originalStageSingleMarking_relativeCartier K n h m i).1 3 (by decide) _

/-- The particular complete cubic coordinates restrict to these original node representatives. -/
theorem completePointStageNodeCubic_completeRatio (k : Fin 3) :
    completePointStageNodeCubic K n h m i j k =
      ((a) ∣_ (C)).appTop ((C).topIso.inv
        ((f).appLE (O) (C) (completePointStageComplement_preimage K n h m i).le
          (sectionRatioOn (L) (s 2) (O) le_rfl (s k)))) := by
  rw [completePointStageNodeCubic_ratio,
    completePointStageProjectiveSections_ratio]

end FLT.Mazur.PolygonInfinitesimalStages
