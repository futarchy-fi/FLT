/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientLocalMap
public import FLT.Mazur.PolygonCompleteBoundaryFactorization

/-!
# Local normalization of the actual complete boundary comparison

The constructed boundary comparison sends the pulled-back coefficient basis
to its original boundary section on each inverse-image generator chart.
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

/-- The complete comparison retains the prescribed original local generator morphism. -/
theorem completeCoefficientBoundaryIso_restrict (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    let c := completeCoefficientCoordinates K n h
    let p := originalStageToCompatibleProj K n h m
    let U := p ⁻¹ᵁ GradedProjLine.chart
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) c.coordinate i
    let M := tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h)
    (restrictFunctor U.ι).map (completeCoefficientBoundaryIso K n h m).hom =
      GradedProjLine.coefficientLocalHom
        (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
        c.coordinate c.homogeneous p M (completeCoefficientBoundarySection K n h m) i := by
  exact GradedProjLine.coefficientComparison_restrict_localHom
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
    (completeCoefficientCoordinates K n h).coordinate
    (completeCoefficientCoordinates K n h).homogeneous
    (originalStageToCompatibleProj K n h m)
    (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
    (completeCoefficientBoundarySection K n h m) (completeCoefficientCoordinates K n h).covers
    (completeCoefficientChart_le_generator K n h m)
    (completeCoefficientTransition_boundary K n h m)
    (completeCoefficientBoundaryIso K n h m).hom
    (completeCoefficientBoundaryIso_factor K n h m) i

end FLT.Mazur.PolygonInfinitesimalStages
