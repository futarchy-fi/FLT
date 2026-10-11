/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteDivisorLineCoherence
public import FLT.Mazur.PolygonCompleteDivisorPowerComparison
public import FLT.Mazur.PolygonCompleteBoundarySectionTransport
public import FLT.Mazur.PolygonCompleteCoefficientCoherence
public import FLT.Mazur.TensorPowerPullbackComparison

/-!
# Original transition coherence of complete marked powers

The canonical complete-to-stage comparisons commute with the original boundary
line transitions, including the specified equality of the composite scheme map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family boundaryLine completeMarkingLine
  ModuleSheafTensor.tensor completeMarkingLineStageIso boundaryLineSystemIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original boundary-line comparison on an arbitrary tensor power. -/
def completeBoundaryPowerTransitionIso (d : ℕ) {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).obj (tensorPower (boundaryLine K b n h) d) ≅
      tensorPower (boundaryLine K a n h) d :=
  tensorPowerPullbackComparison ((stageSystem K n h).map f) (boundaryLineSystemIso K n h f) d

/-- At the coefficient exponent, the transition is exactly the original boundary-power map. -/
theorem completeBoundaryPowerTransitionIso_coefficient {a b : ℕ} (f : a ⟶ b) :
    completeBoundaryPowerTransitionIso K n h (completeCoefficientBoundaryExponent K n h) f =
      completeBoundaryPowerStageIso K n h f := rfl

/-- Every marked tensor-power comparison respects the original stage transitions. -/
theorem completeMarkingPowerStageIso_transition (d : ℕ) {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).map (completeMarkingPowerStageIso K n h d b).hom ≫
        (completeBoundaryPowerTransitionIso K n h d f).hom =
      (completeLineStageTransitionIso K n h (tensorPower (completeMarkingLine K n h) d) f).hom ≫
        (completeMarkingPowerStageIso K n h d a).hom := by
  rw [completeLineStageTransitionIso_eq_sealed]
  apply tensorPowerPullbackComparison_stage
    (originalStageToCompatibleProj K n h a) (originalStageToCompatibleProj K n h b)
    ((stageSystem K n h).map f) (originalStageToCompatibleProj_naturality K n h f)
    (completeMarkingLineStageIso K n h b) (boundaryLineSystemIso K n h f)
    (completeMarkingLineStageIso K n h a)
  rw [← completeLineStageTransitionIso_eq_sealed]
  exact completeMarkingLineStageIso_transition_hom K n h f

end FLT.Mazur.PolygonInfinitesimalStages
