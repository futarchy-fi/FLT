/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedSectionTransport
public import FLT.Mazur.PolygonCompleteCoefficientAmple

/-!
# The total-space charts of reconstructed marked coordinates

The section identity identifies individual generator opens with their original
homogeneous charts on the complete family, and proves each is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] completeCoefficientCoordinates completeCoefficientBoundaryExponent
  completeCoefficientMarkedIso completeMarkedPowerModelIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Each reconstructed marked coordinate generates on exactly its original total-space chart. -/
theorem completeMarkedModelCoordinate_generatorOpen
    (i : (completeCoefficientCoordinates K n h).Index) :
    sectionGeneratorOpen
        (completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h))
        (completeMarkedModelCoordinate K n h i) =
      GradedProjLine.chart (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
        (completeCoefficientCoordinates K n h).coordinate i := by
  rw [completeMarkedModelCoordinate_eq_transport]
  exact (sectionGeneratorOpen_iso
    (completeMarkedPowerModelIso K n h (completeCoefficientBoundaryExponent K n h)).symm
    ((completeCoefficientMarkedIso K n h).hom.app ⊤ (completeCoefficientSection K n h i))).trans
      ((sectionGeneratorOpen_iso (completeCoefficientMarkedIso K n h)
        (completeCoefficientSection K n h i)).trans
          (completeCoefficientSection_generatorOpen K n h i))

/-- Every reconstructed marked coordinate has an affine generator open on the total family. -/
theorem completeMarkedModelCoordinate_isAffineOpen
    (i : (completeCoefficientCoordinates K n h).Index) :
    IsAffineOpen (sectionGeneratorOpen
      (completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h))
      (completeMarkedModelCoordinate K n h i)) := by
  rw [completeMarkedModelCoordinate_generatorOpen]
  exact Proj.isAffineOpen_basicOpen _ _
    ((completeCoefficientCoordinates K n h).homogeneous i)
    (completeCoefficientCoordinates K n h).positive

end FLT.Mazur.PolygonInfinitesimalStages
