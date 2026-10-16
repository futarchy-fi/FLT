/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointStagePoleSections
public import FLT.Mazur.ModuleComparedMarkingFrame

/-!
# The retained pole coefficients along the original stage marking

The complete marking frames induce actual frames on every full stage.
The chosen pole-two and pole-three lifts still have coefficient one, and
the original homogeneous triple still has coefficients [0, 1, 0].
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "f" => originalStageToCompatibleProj K n h m
local notation "p" => marking K m n h i
local notation "s" => completeBaseMarking K n h i
local notation "b" => baseToSeries K m
local notation "L" => completePointLine K n h i
local notation "M" => originalStageSinglePointLine K n h m i

/-- The actual complete marking frame transported along the original full stage square. -/
def completePointStagePoleFrame (d : ℕ) :
    (pullback (p)).obj (tensorPower (M) d) ≅ structureModule (Spec (.of (Ring K m))) :=
  comparedMarkingFrame (f) (p) (s) (b)
    (baseToSeries_completeBaseMarking K n h i m).symm
    (completePointPowerOriginalStageIso K n h m i d)
    (sectionPoleMultiplicativeFrame (s) (completeBaseMarking_relativeCartier K n h i).1
      (completePointSectionFrame K n h i) d)

/-- The coefficient of a stage section in the retained complete marking frame. -/
def completePointStagePoleCoefficient (d : ℕ) (t : Γ(tensorPower (M) d, ⊤)) :
    Γ(Spec (.of (Ring K m)), ⊤) :=
  (completePointStagePoleFrame K n h m i d).hom.app ⊤ (pullGlobal (p) _ t)

/-- The actual coefficient restriction uses the unchanged original base morphism. -/
theorem completePointStagePoleCoefficient_transport (d : ℕ)
    (t : Γ(tensorPower (L) d, ⊤)) :
    completePointStagePoleCoefficient K n h m i d
        (completePointPowerStageSection K n h m i d t) =
      (b).appTop (sectionPoleCoefficient (s)
        (completeBaseMarking_relativeCartier K n h i).1
        (completePointSectionFrame K n h i) d t) :=
  comparedMarkingFrame_section (f) (p) (s) (b)
    (baseToSeries_completeBaseMarking K n h i m).symm
    (completePointPowerOriginalStageIso K n h m i d)
    (sectionPoleMultiplicativeFrame (s) (completeBaseMarking_relativeCartier K n h i).1
      (completePointSectionFrame K n h i) d) t

/-- The transported order-two lift has coefficient one on the entire stage marking. -/
theorem completePointStagePoleTwo_coefficient :
    completePointStagePoleCoefficient K n h m i 2 (completePointStagePoleTwo K n h m i) =
      1 := by
  rw [completePointStagePoleTwo, completePointStagePoleCoefficient_transport,
    completePointPoleTwoSection_coefficient, map_one]

/-- The transported order-three lift has coefficient one on the entire stage marking. -/
theorem completePointStagePoleThree_coefficient :
    completePointStagePoleCoefficient K n h m i 3
      (completePointStagePoleThree K n h m i) = 1 := by
  rw [completePointStagePoleThree, completePointStagePoleCoefficient_transport,
    completePointProjectiveY_coefficient, map_one]

/-- The original homogeneous coordinate table survives with all stage nilpotents. -/
theorem completePointStageProjectiveSections_coefficient (j : Fin 3) :
    completePointStagePoleCoefficient K n h m i 3
        (completePointStageProjectiveSections K n h m i j) =
      (![0, 1, 0] : Fin 3 → Γ(Spec (.of (Ring K m)), ⊤)) j := by
  rw [completePointStageProjectiveSections, completePointStagePoleCoefficient_transport,
    completePointProjectiveSections_coefficient]
  fin_cases j
  · exact map_zero (b).appTop.hom
  · exact map_one (b).appTop.hom
  · exact map_zero (b).appTop.hom

end FLT.Mazur.PolygonInfinitesimalStages
