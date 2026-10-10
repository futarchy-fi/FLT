/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjLineTransitionEvaluation
public import FLT.Mazur.ModuleSectionCocycleIso
public import FLT.Mazur.PolygonCompleteCoordinateEvaluation

/-!
# The complete coefficient line restricts to the original boundary power

The actual pullback cocycle has the ratios of the evaluated original
sections. Their generating maps glue to an isomorphism with the original
boundary tensor power on each original infinitesimal stage.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  originalStageToCompatibleProj SectionRetainedProjConstruction.toProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual inverse-image charts are contained in the original section generator opens. -/
theorem completeCoefficientChart_le_generator (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    originalStageToCompatibleProj K n h m ⁻¹ᵁ
        GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate i ≤
      sectionGeneratorOpen
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
        (completeCoefficientBoundarySection K n h m i) :=
  (completeCoefficientChart_preimage K n h m i).le

/-- Every pulled-back coefficient transition is the ratio of the original boundary sections. -/
theorem completeCoefficientTransition_boundary (m : ℕ)
    (i j : (completeCoefficientCoordinates K n h).Index)
    (U : (family K m n h).left.Opens)
    (hi : U ≤ originalStageToCompatibleProj K n h m ⁻¹ᵁ
      GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate i)
    (hj : U ≤ originalStageToCompatibleProj K n h m ⁻¹ᵁ
      GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate j) :
    (((GradedProjLine.cocycle _ (completeCoefficientCoordinates K n h).coordinate
        (completeCoefficientCoordinates K n h).homogeneous 1).inverseImage
        (originalStageToCompatibleProj K n h m)).unit i j U hi hj :
          Γ((family K m n h).left, U)) =
      sectionRatioOn
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
        (completeCoefficientBoundarySection K n h m i) U
        (hi.trans (completeCoefficientChart_le_generator K n h m i))
        (completeCoefficientBoundarySection K n h m j) := by
  rw [GradedProjLine.coefficient_inverseImage_unit]
  exact originalStage_coordinate_ratio K n h m _ (completeCoefficientCoordinates K n h).positive
    _ _ ((completeCoefficientCoordinates K n h).homogeneous i)
    ((completeCoefficientCoordinates K n h).homogeneous j) U _

/-- The constructed complete line pulls back to the original positive boundary tensor power. -/
def completeCoefficientBoundaryIso (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj (completeCoefficientLine K n h) ≅
      tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h) := by
  let c := completeCoefficientCoordinates K n h
  let g := GradedProjLine.cocycle _ c.coordinate c.homogeneous 1
  let p := originalStageToCompatibleProj K n h m
  exact g.pullbackIso p c.covers ≪≫
    sectionCocycleIso _ (fun i ↦ p ⁻¹ᵁ GradedProjLine.chart _ c.coordinate i)
      (completeCoefficientBoundarySection K n h m)
      (completeCoefficientChart_le_generator K n h m) (g.inverseImage p)
      (ModuleSheafUnitCocycle.Cocycle.inverseImage_cover p c.covers)
      (completeCoefficientTransition_boundary K n h m)

end FLT.Mazur.PolygonInfinitesimalStages
