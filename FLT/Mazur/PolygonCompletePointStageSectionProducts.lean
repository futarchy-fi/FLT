/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleComparedTensorSectionProduct
public import FLT.Mazur.PolygonCompletePointStagePoleCoefficients

/-!
# Products of retained complete sections on the original full stage

The complete-to-stage comparison is the genuine tensor-power comparison.
It carries products of the original sections to products of their stage
transports. The retained pole-frame coefficients multiply on these sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
  completePointLineOriginalStageIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "L" => completePointLine K n h i
local notation "M" => originalStageSinglePointLine K n h m i
local notation "S" => completePointPowerStageSection K n h m i

/-- The original stage transport retains homogeneous products of complete sections. -/
theorem completePointPowerStageSection_product (d k : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (v : Γ(tensorPower (L) k, ⊤)) :
    S (d + k) (SectionGradedMultiplication.mul (L) ⊤ d k s v) =
      SectionGradedMultiplication.mul (M) ⊤ d k (S d s) (S k v) :=
  tensorPowerPullbackComparison_product (originalStageToCompatibleProj K n h m)
    (completePointLineOriginalStageIso K n h m i) d k s v

/-- The retained complete pole frame multiplies coefficients of original transported sections. -/
theorem completePointStagePoleCoefficient_product (d k : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (v : Γ(tensorPower (L) k, ⊤)) :
    completePointStagePoleCoefficient K n h m i (d + k)
      (SectionGradedMultiplication.mul (M) ⊤ d k (S d s) (S k v)) =
        completePointStagePoleCoefficient K n h m i d (S d s) *
          completePointStagePoleCoefficient K n h m i k (S k v) := by
  rw [← completePointPowerStageSection_product]
  simp only [completePointStagePoleCoefficient_transport]
  exact (congrArg (baseToSeries K m).appTop
    (sectionPoleCoefficient_mul (completeBaseMarking K n h i)
      (completeBaseMarking_relativeCartier K n h i).1
      (completePointSectionFrame K n h i) d k s v)).trans
        ((baseToSeries K m).appTop.hom.map_mul _ _)

end FLT.Mazur.PolygonInfinitesimalStages
