/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedCoordinateCharts
public import FLT.Mazur.GradedProjCoefficientRatios
public import FLT.Mazur.ModuleSectionRatioOpenIso

/-!
# Original homogeneous ratios on the complete marked family

On every original chart subopen, the ratio of reconstructed marked coordinates
is exactly the original homogeneous fraction, with its original normalization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] completeCoefficientCoordinates completeCoefficientBoundaryExponent
  completeCoefficientMarkedIso completeMarkedPowerModelIso ModuleSheafTensor.tensor
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Reconstructed coordinate ratios on any generator subopen are the original coefficient ratios. -/
theorem completeMarkedModelCoordinate_ratio_transport
    (i j : (completeCoefficientCoordinates K n h).Index)
    (U : (exactVeroneseProj K n h).Opens)
    (hi : U ≤ sectionGeneratorOpen (completeCoefficientLine K n h)
      (completeCoefficientSection K n h i)) :
    sectionRatioOn
        (completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h))
        (completeMarkedModelCoordinate K n h i) U
        (by simpa only [completeMarkedModelCoordinate_generatorOpen,
          completeCoefficientSection_generatorOpen] using hi)
        (completeMarkedModelCoordinate K n h j) =
      sectionRatioOn (completeCoefficientLine K n h) (completeCoefficientSection K n h i) U hi
        (completeCoefficientSection K n h j) := by
  let e := completeCoefficientMarkedIso K n h ≪≫
    (completeMarkedPowerModelIso K n h (completeCoefficientBoundaryExponent K n h)).symm
  have he (k : (completeCoefficientCoordinates K n h).Index) :
      completeMarkedModelCoordinate K n h k = e.hom.app ⊤ (completeCoefficientSection K n h k) :=
    completeMarkedModelCoordinate_eq_transport K n h k
  simpa only [he] using sectionRatioOn_iso e
    (completeCoefficientSection K n h i) (completeCoefficientSection K n h j) U hi

/-- The marked transition ratio is the original homogeneous fraction on every chart subopen. -/
theorem completeMarkedModelCoordinate_ratio
    (i j : (completeCoefficientCoordinates K n h).Index)
    (U : (exactVeroneseProj K n h).Opens)
    (hi : U ≤ GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate i) :
    sectionRatioOn
        (completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h))
        (completeMarkedModelCoordinate K n h i) U
        (by simpa only [completeMarkedModelCoordinate_generatorOpen] using hi)
        (completeMarkedModelCoordinate K n h j) =
      (exactVeroneseProj K n h).presheaf.map (homOfLE hi).op
        (Proj.awayToSection (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
          ((completeCoefficientCoordinates K n h).coordinate i)
          (GradedProjLine.coordinate _ (completeCoefficientCoordinates K n h).coordinate
            (completeCoefficientCoordinates K n h).homogeneous i j)) := by
  have hi' : U ≤ sectionGeneratorOpen (completeCoefficientLine K n h)
      (completeCoefficientSection K n h i) := by
    simpa only [completeCoefficientSection_generatorOpen] using hi
  exact (completeMarkedModelCoordinate_ratio_transport K n h i j U hi').trans
    (GradedProjLine.coefficientSection_ratio _ _
      (completeCoefficientCoordinates K n h).homogeneous
      (completeCoefficientCoordinates K n h).positive
      (completeCoefficientCoordinates K n h).covers i j U hi)

end FLT.Mazur.PolygonInfinitesimalStages
