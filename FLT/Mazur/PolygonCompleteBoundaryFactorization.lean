/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryLineComparison

/-!
# Factorization of the actual complete boundary comparison

Expose the defining two descent maps without expanding their sheaf implementations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  originalStageToCompatibleProj ModuleSheafTensor.tensor sectionCocycleIso
  ModuleSheafUnitCocycle.Cocycle.sheaf GradedProjLine.cocycle
  tensorPower completeCoefficientBoundaryExponent
  completeCoefficientBoundarySection modulePullbackTrivialization
  completeCoefficientBoundaryIso ModuleSheafUnitCocycle.Cocycle.pullbackIso


variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete comparison is the composite of the two original descent maps. -/
theorem completeCoefficientBoundaryIso_factor (m : ℕ) :
    let c := completeCoefficientCoordinates K n h
    let p := originalStageToCompatibleProj K n h m
    let g := GradedProjLine.cocycle
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
      c.coordinate c.homogeneous 1
    (completeCoefficientBoundaryIso K n h m).hom =
      (g.pullbackIso p c.covers).hom ≫
        (sectionCocycleIso
          (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
          (fun i ↦ p ⁻¹ᵁ GradedProjLine.chart
            (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) c.coordinate i)
          (completeCoefficientBoundarySection K n h m)
          (completeCoefficientChart_le_generator K n h m) (g.inverseImage p)
          (ModuleSheafUnitCocycle.Cocycle.inverseImage_cover p c.covers)
          (completeCoefficientTransition_boundary K n h m)).hom := by
  delta completeCoefficientBoundaryIso
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
