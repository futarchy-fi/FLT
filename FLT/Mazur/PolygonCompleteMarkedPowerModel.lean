/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingPowerCoherence
public import FLT.Mazur.ModulePullbackComparisonTransport

/-!
# Coherent powers of the actual marked line models

The complete and boundary powers keep opaque line objects and use the
canonical tensor pullback comparisons of the original marked lines.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family ModuleSheafTensor.tensor
  completeMarkingLine boundaryLine completeMarkingPowerStageIso completeBoundaryPowerTransitionIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual complete marked power with its implementation sealed. -/
irreducible_def completeMarkedPowerModel (d : ℕ) : (exactVeroneseProj K n h).Modules :=
  tensorPower (completeMarkingLine K n h) d

/-- The actual boundary marked power with its implementation sealed. -/
irreducible_def completeMarkedBoundaryPowerModel (d m : ℕ) : (family K m n h).left.Modules :=
  tensorPower (boundaryLine K m n h) d

/-- The complete model is the power of the actual complete marked line. -/
def completeMarkedPowerModelIso (d : ℕ) :
    completeMarkedPowerModel K n h d ≅ tensorPower (completeMarkingLine K n h) d :=
  eqToIso (completeMarkedPowerModel_def K n h d)

/-- The boundary model is the power of the actual boundary marked line. -/
def completeMarkedBoundaryPowerModelIso (d m : ℕ) :
    completeMarkedBoundaryPowerModel K n h d m ≅
      tensorPower (boundaryLine K m n h) d :=
  eqToIso (completeMarkedBoundaryPowerModel_def K n h d m)

/-- Every complete marked power remains a line bundle. -/
theorem completeMarkedPowerModel_rankOne (d : ℕ) :
    LocallyFreeRankOne (completeMarkedPowerModel K n h d) := by
  rw [completeMarkedPowerModel_def]
  exact (completeMarkingLine_rankOne K n h).tensorPower d

/-- The original complete-to-stage comparison transported to opaque power models. -/
def completeMarkedPowerModelStageIso (d m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj (completeMarkedPowerModel K n h d) ≅
      completeMarkedBoundaryPowerModel K n h d m :=
  (pullback (originalStageToCompatibleProj K n h m)).mapIso (completeMarkedPowerModelIso K n h d) ≪≫
    completeMarkingPowerStageIso K n h d m ≪≫ (completeMarkedBoundaryPowerModelIso K n h d m).symm

/-- The original boundary-power transition transported to opaque power models. -/
def completeMarkedPowerModelTransition (d : ℕ) {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).obj (completeMarkedBoundaryPowerModel K n h d b) ≅
      completeMarkedBoundaryPowerModel K n h d a :=
  (pullback ((stageSystem K n h).map f)).mapIso (completeMarkedBoundaryPowerModelIso K n h d b) ≪≫
    completeBoundaryPowerTransitionIso K n h d f ≪≫
      (completeMarkedBoundaryPowerModelIso K n h d a).symm

/-- All power-model comparisons retain the original commuting stage square. -/
theorem completeMarkedPowerModelStageIso_transition (d : ℕ) {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).map (completeMarkedPowerModelStageIso K n h d b).hom ≫
        (completeMarkedPowerModelTransition K n h d f).hom =
      (completeLineStageTransitionIso K n h (completeMarkedPowerModel K n h d) f).hom ≫
        (completeMarkedPowerModelStageIso K n h d a).hom := by
  rw [completeLineStageTransitionIso_eq_sealed]
  apply pullbackComparison_transport
    (originalStageToCompatibleProj K n h a) (originalStageToCompatibleProj K n h b)
    ((stageSystem K n h).map f) (originalStageToCompatibleProj_naturality K n h f)
    (completeMarkedPowerModelIso K n h d) (completeMarkedBoundaryPowerModelIso K n h d b)
    (completeMarkedBoundaryPowerModelIso K n h d a) (completeMarkingPowerStageIso K n h d b)
    (completeBoundaryPowerTransitionIso K n h d f) (completeMarkingPowerStageIso K n h d a)
  rw [← completeLineStageTransitionIso_eq_sealed]
  exact completeMarkingPowerStageIso_transition K n h d f

end FLT.Mazur.PolygonInfinitesimalStages
