/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedCoordinates
public import FLT.Mazur.LineBundleSectionOpenPullback

/-!
# Generator opens of reconstructed marked coordinates on the original stages

The actual reconstructed sections recover exactly the original coordinate
charts after every infinitesimal restriction, including the closed stage.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family originalStageToCompatibleProj
  completeCoefficientCoordinates completeCoefficientBoundaryExponent
  completeMarkedPowerModelStageIso completeMarkedBoundaryPowerModelIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A modeled boundary coordinate has exactly its original generator open. -/
theorem completeMarkedBoundaryModelCoordinate_generatorOpen (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    sectionGeneratorOpen
        (completeMarkedBoundaryPowerModel K n h (completeCoefficientBoundaryExponent K n h) m)
        (completeMarkedBoundaryModelCoordinate K n h m i) =
      sectionGeneratorOpen
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
        (completeCoefficientBoundarySection K n h m i) := by
  exact sectionGeneratorOpen_iso
    (completeMarkedBoundaryPowerModelIso K n h (completeCoefficientBoundaryExponent K n h) m).symm
    (completeCoefficientBoundarySection K n h m i)

/-- Reconstructed coordinate generator opens recover the original chart on every stage. -/
theorem completeMarkedModelCoordinate_generatorOpen_preimage (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    originalStageToCompatibleProj K n h m ⁻¹ᵁ
        sectionGeneratorOpen
          (completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h))
          (completeMarkedModelCoordinate K n h i) =
      originalStageToCompatibleProj K n h m ⁻¹ᵁ
        GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate i := by
  rw [← sectionGeneratorOpen_pullGlobal (completeMarkedPowerModel_rankOne K n h _),
    completeCoefficientChart_preimage]
  rw [← sectionGeneratorOpen_iso (completeMarkedPowerModelStageIso K n h
    (completeCoefficientBoundaryExponent K n h) m), completeMarkedModelCoordinate_stage]
  exact completeMarkedBoundaryModelCoordinate_generatorOpen K n h m i

end FLT.Mazur.PolygonInfinitesimalStages
