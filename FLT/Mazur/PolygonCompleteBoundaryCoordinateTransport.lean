/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientSectionTransport
public import FLT.Mazur.PolygonCompleteBoundaryLocalComparison

/-!
# Actual coordinate sections under the complete boundary comparison

Each original homogeneous coordinate defines a global coefficient section.
Its image under the constructed boundary comparison is the original
boundary section, without choosing or rescaling another generator.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  originalStageToCompatibleProj completeCoefficientBoundaryIso ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual original coordinate section of the complete coefficient line. -/
def completeCoefficientSection (i : (completeCoefficientCoordinates K n h).Index) :
    Γ(completeCoefficientLine K n h, ⊤) :=
  GradedProjLine.coefficientSection
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
    (completeCoefficientCoordinates K n h).coordinate
    (completeCoefficientCoordinates K n h).homogeneous i

/-- The actual comparison sends each pulled coordinate to its original boundary section. -/
theorem completeCoefficientBoundaryIso_section (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    (completeCoefficientBoundaryIso K n h m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj K n h m) (completeCoefficientLine K n h)
          (completeCoefficientSection K n h i)) =
      completeCoefficientBoundarySection K n h m i := by
  let c := completeCoefficientCoordinates K n h
  apply GradedProjLine.coefficientSection_image
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) c.coordinate c.homogeneous
    (originalStageToCompatibleProj K n h m) c.covers
    (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
    (completeCoefficientBoundarySection K n h m)
    (completeCoefficientChart_le_generator K n h m)
    (completeCoefficientBoundaryIso K n h m).hom
    (completeCoefficientBoundaryIso_restrict K n h m)
  intro j k U hU
  exact originalStage_coordinate_ratio K n h m c.degree c.positive
    (c.coordinate j) (c.coordinate k) (c.homogeneous j) (c.homogeneous k) U
    (hU.trans (completeCoefficientChart_le_generator K n h m j))

end FLT.Mazur.PolygonInfinitesimalStages
