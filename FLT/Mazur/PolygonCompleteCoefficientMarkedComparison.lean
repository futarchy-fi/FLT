/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteLineIsoReconstruction
public import FLT.Mazur.PolygonCompleteMarkingPowerCoherence
public import FLT.Mazur.PolygonCompleteBoundaryTransitionCoherence
public import FLT.Mazur.ModulePullbackComparisonRatio

/-!
# The global coefficient line is the original complete marked power

Both actual lines have coherent identifications with the same original
boundary power. Reconstruction gives their unique global comparison,
retaining the prescribed isomorphism on every original stage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj family
  ModuleSheafTensor.tensor completeCoefficientLine completeMarkingLine boundaryLine
  completeCoefficientBoundaryIso completeMarkingPowerStageIso completeCoefficientBoundaryExponent
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The prescribed comparison between the coefficient and marked lines on each original stage. -/
def completeCoefficientMarkedStageIso (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj (completeCoefficientLine K n h) ≅
      (pullback (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (completeMarkingLine K n h) (completeCoefficientBoundaryExponent K n h)) :=
  completeCoefficientBoundaryIso K n h m ≪≫
    (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) m).symm

/-- The prescribed original coefficient-to-marked comparisons form a commuting stage square. -/
theorem completeCoefficientMarkedStageIso_transition {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).map (completeCoefficientMarkedStageIso K n h b).hom ≫
        (completeLineStageTransitionIso K n h
          (tensorPower (completeMarkingLine K n h) (completeCoefficientBoundaryExponent K n h))
          f).hom =
      (completeLineStageTransitionIso K n h (completeCoefficientLine K n h) f).hom ≫
        (completeCoefficientMarkedStageIso K n h a).hom := by
  simp only [completeLineStageTransitionIso_eq_sealed]
  apply pullbackComparison_ratio
    (originalStageToCompatibleProj K n h a) (originalStageToCompatibleProj K n h b)
    ((stageSystem K n h).map f) (originalStageToCompatibleProj_naturality K n h f)
    (completeCoefficientBoundaryIso K n h a) (completeCoefficientBoundaryIso K n h b)
    (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) a)
    (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) b)
    (completeBoundaryPowerStageIso K n h f).hom
  · simpa only [completeLineStageTransitionIso_eq_sealed] using
      completeCoefficientBoundaryIso_transition K n h f
  · simpa only [completeLineStageTransitionIso_eq_sealed,
      completeBoundaryPowerTransitionIso_coefficient] using
      completeMarkingPowerStageIso_transition K n h (completeCoefficientBoundaryExponent K n h) f

/-- The prescribed original stage comparisons have a unique global isomorphism. -/
theorem completeCoefficientMarkedIso_existsUnique :
    ∃! e : completeCoefficientLine K n h ≅
      tensorPower (completeMarkingLine K n h) (completeCoefficientBoundaryExponent K n h),
      ∀ m, (pullback (originalStageToCompatibleProj K n h m)).mapIso e =
        completeCoefficientMarkedStageIso K n h m := by
  exact completeLineIso_existsUnique K n h (completeCoefficientLine_rankOne K n h)
    ((completeMarkingLine_rankOne K n h).tensorPower _)
    (completeCoefficientMarkedStageIso K n h)
    (fun {_ _} f ↦ completeCoefficientMarkedStageIso_transition K n h f)

/-- The coefficient line is canonically the actual positive power of the complete marking line. -/
def completeCoefficientMarkedIso : completeCoefficientLine K n h ≅
    tensorPower (completeMarkingLine K n h) (completeCoefficientBoundaryExponent K n h) :=
  (completeCoefficientMarkedIso_existsUnique K n h).exists.choose

/-- The reconstructed global comparison retains every prescribed original-stage comparison. -/
theorem completeCoefficientMarkedIso_stage (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).mapIso
        (completeCoefficientMarkedIso K n h) = completeCoefficientMarkedStageIso K n h m :=
  (completeCoefficientMarkedIso_existsUnique K n h).exists.choose_spec m

end FLT.Mazur.PolygonInfinitesimalStages
