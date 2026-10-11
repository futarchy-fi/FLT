/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedPowerSections
public import FLT.Mazur.ModulePullbackSectionIsoTransport

/-!
# Reconstructing original homogeneous coordinates on the complete marked power

The compatible original boundary coordinates have unique lifts to the actual
complete marked power, represented by its canonically identified opaque model.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family originalStageToCompatibleProj
  exactVeroneseProj exactVeroneseProjToBase boundaryLine completeCoefficientCoordinates
  completeCoefficientBoundaryExponent ModuleSheafTensor.tensor completeBoundaryPowerStageIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original homogeneous boundary coordinate in the canonical opaque power model. -/
def completeMarkedBoundaryModelCoordinate (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    Γ(completeMarkedBoundaryPowerModel K n h (completeCoefficientBoundaryExponent K n h) m, ⊤) :=
  (completeMarkedBoundaryPowerModelIso K n h (completeCoefficientBoundaryExponent K n h) m).inv.app
    ⊤ (completeCoefficientBoundarySection K n h m i)

/-- The original homogeneous coordinates remain compatible in the power models. -/
theorem completeMarkedBoundaryModelCoordinate_transition {a b : ℕ} (f : a ⟶ b)
    (i : (completeCoefficientCoordinates K n h).Index) :
    (completeMarkedPowerModelTransition K n h (completeCoefficientBoundaryExponent K n h) f).hom.app
        ⊤ (pullGlobal ((stageSystem K n h).map f) _
          (completeMarkedBoundaryModelCoordinate K n h b i)) =
      completeMarkedBoundaryModelCoordinate K n h a i := by
  have ht := pullbackSection_transport_inv
    ((stageSystem K n h).map f)
    (completeMarkedBoundaryPowerModelIso K n h (completeCoefficientBoundaryExponent K n h) b)
    (completeMarkedBoundaryPowerModelIso K n h (completeCoefficientBoundaryExponent K n h) a)
    (completeBoundaryPowerTransitionIso K n h (completeCoefficientBoundaryExponent K n h) f)
    (completeCoefficientBoundarySection K n h b i)
  rw [completeBoundaryPowerTransitionIso_coefficient, completeBoundaryPowerStageIso_section] at ht
  simpa only [completeMarkedPowerModelTransition, completeBoundaryPowerTransitionIso_coefficient,
    completeMarkedBoundaryModelCoordinate] using ht

/-- Every original homogeneous coordinate has a unique complete marked-power lift. -/
theorem completeMarkedCoordinate_existsUnique
    (i : (completeCoefficientCoordinates K n h).Index) :
    ∃! t : Γ(completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h), ⊤),
      ∀ m, (completeMarkedPowerModelStageIso K n h
        (completeCoefficientBoundaryExponent K n h) m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj K n h m) _ t) =
          completeMarkedBoundaryModelCoordinate K n h m i := by
  exact completeMarkedPowerModelSection_existsUnique K n h
    (completeCoefficientBoundaryExponent K n h)
    (fun m ↦ completeMarkedBoundaryModelCoordinate K n h m i)
    (fun _ _ hab ↦ completeMarkedBoundaryModelCoordinate_transition K n h (homOfLE hab) i)

/-- The uniquely reconstructed original homogeneous coordinate on the marked power. -/
def completeMarkedModelCoordinate (i : (completeCoefficientCoordinates K n h).Index) :
    Γ(completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h), ⊤) :=
  (completeMarkedCoordinate_existsUnique K n h i).exists.choose

/-- Every reconstructed marked coordinate has the prescribed original boundary value. -/
theorem completeMarkedModelCoordinate_stage
    (i : (completeCoefficientCoordinates K n h).Index) (m : ℕ) :
    (completeMarkedPowerModelStageIso K n h (completeCoefficientBoundaryExponent K n h) m).hom.app
      ⊤ (pullGlobal (originalStageToCompatibleProj K n h m) _
        (completeMarkedModelCoordinate K n h i)) =
      completeMarkedBoundaryModelCoordinate K n h m i :=
  (completeMarkedCoordinate_existsUnique K n h i).exists.choose_spec m

end FLT.Mazur.PolygonInfinitesimalStages
