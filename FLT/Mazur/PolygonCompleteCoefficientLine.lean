/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjEqualDegreeCover
public import FLT.Mazur.GradedProjLineSheaf
public import FLT.Mazur.PolygonVeroneseProperProj

/-!
# A coherent coefficient line on the actual compatible Proj

Finite homogeneous generators supply a common-degree cover of the original
complete-base candidate. Its original homogeneous ratios glue a line sheaf.
Comparison with powers of the original boundary lines is a separate theorem.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A finite equal-degree cover of the actual compatible Veronese algebra. -/
def completeCoefficientCoordinates : GradedProjEqualDegreeCover.Coordinates
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) := by
  let _ := exactVeronese_finiteType_zero K n h
  exact Classical.choice (GradedProjEqualDegreeCover.nonempty_coordinates _)

/-- The coefficient line constructed from actual homogeneous ratios on the candidate. -/
def completeCoefficientLine : (exactVeroneseProj K n h).Modules :=
  GradedProjLine.line _ (completeCoefficientCoordinates K n h).coordinate
    (completeCoefficientCoordinates K n h).homogeneous 1

/-- The chosen original coordinate charts trivialize the constructed line. -/
def completeCoefficientLineChartIso (i : (completeCoefficientCoordinates K n h).Index) :
    (completeCoefficientLine K n h).restrict
        (GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate i).ι ≅
      structureModule
        (GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate i).toScheme :=
  GradedProjLine.lineRestrictIso _ (completeCoefficientCoordinates K n h).coordinate
    (completeCoefficientCoordinates K n h).homogeneous 1 i

/-- The actual coefficient sheaf is locally free of rank one. -/
theorem completeCoefficientLine_rankOne : LocallyFreeRankOne (completeCoefficientLine K n h) :=
  GradedProjLine.line_rankOne _ (completeCoefficientCoordinates K n h).coordinate
    (completeCoefficientCoordinates K n h).homogeneous 1
    (completeCoefficientCoordinates K n h).covers

/-- The coefficient line is finitely presented on the complete candidate. -/
theorem completeCoefficientLine_isFinitePresentation :
    (completeCoefficientLine K n h).IsFinitePresentation :=
  (completeCoefficientLine_rankOne K n h).isFinitePresentation

end FLT.Mazur.PolygonInfinitesimalStages
