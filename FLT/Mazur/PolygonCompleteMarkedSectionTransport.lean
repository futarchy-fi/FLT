/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientMarkedComparison
public import FLT.Mazur.PolygonCompleteMarkedCoordinates
public import FLT.Mazur.ModulePullbackComparedSection

/-!
# Original coefficient sections on the actual complete marked power

The global comparison retains the original boundary sections. Transport to
its opaque model identifies these sections with the unique reconstructed coordinates.
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
  completeCoefficientCoordinates completeCoefficientMarkedIso completeMarkedPowerModelIso
  completeMarkedBoundaryPowerModelIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The global coefficient comparison sends each section to its prescribed boundary value. -/
theorem completeCoefficientMarkedIso_section_stage (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) m).hom.app
        ⊤ (pullGlobal (originalStageToCompatibleProj K n h m) _
          ((completeCoefficientMarkedIso K n h).hom.app ⊤
            (completeCoefficientSection K n h i))) =
      completeCoefficientBoundarySection K n h m i := by
  exact (pullbackComparedSection (originalStageToCompatibleProj K n h m)
    (completeCoefficientMarkedIso K n h) (completeCoefficientBoundaryIso K n h m)
    (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) m)
    (completeCoefficientMarkedIso_stage K n h m) (completeCoefficientSection K n h i)).trans
      (completeCoefficientBoundaryIso_section K n h m i)

/-- The reconstructed coordinate is exactly the original coefficient section in the power model. -/
theorem completeMarkedModelCoordinate_eq_transport
    (i : (completeCoefficientCoordinates K n h).Index) :
    completeMarkedModelCoordinate K n h i =
      (completeMarkedPowerModelIso K n h (completeCoefficientBoundaryExponent K n h)).inv.app ⊤
        ((completeCoefficientMarkedIso K n h).hom.app ⊤
          (completeCoefficientSection K n h i)) := by
  apply ((completeMarkedCoordinate_existsUnique K n h i).unique
    (completeMarkedModelCoordinate_stage K n h i) ?_)
  intro m
  have ht := pullbackSection_transport_inv (originalStageToCompatibleProj K n h m)
    (completeMarkedPowerModelIso K n h (completeCoefficientBoundaryExponent K n h))
    (completeMarkedBoundaryPowerModelIso K n h (completeCoefficientBoundaryExponent K n h) m)
    (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) m)
    ((completeCoefficientMarkedIso K n h).hom.app ⊤ (completeCoefficientSection K n h i))
  rw [completeCoefficientMarkedIso_section_stage] at ht
  exact ht

end FLT.Mazur.PolygonInfinitesimalStages
