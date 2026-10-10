/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientOpens
public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Original tensor-power transport of the chosen boundary coordinates

The chosen complete coordinates commute with the original tensor-power
pullback isomorphisms, expressed as actual module maps and section pullbacks.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage line comparison induces its actual boundary-power comparison. -/
def completeBoundaryPowerStageIso {a b : ℕ} (f : a ⟶ b) :
    (pullback ((stageSystem K n h).map f)).obj
        (tensorPower (boundaryLine K b n h) (completeCoefficientBoundaryExponent K n h)) ≅
      tensorPower (boundaryLine K a n h) (completeCoefficientBoundaryExponent K n h) :=
  tensorPowerIso ((stageSystem K n h).map f) (boundaryLine K b n h)
      (completeCoefficientBoundaryExponent K n h) ≪≫
    tensorPowerCongr (boundaryLineSystemIso K n h f) (completeCoefficientBoundaryExponent K n h)

/-- The chosen coordinates commute with the original boundary tensor-power comparison. -/
theorem completeBoundaryPowerStageIso_section {a b : ℕ} (f : a ⟶ b)
    (i : (completeCoefficientCoordinates K n h).Index) :
    (completeBoundaryPowerStageIso K n h f).hom.app ⊤
        (pullGlobal ((stageSystem K n h).map f)
          (tensorPower (boundaryLine K b n h) (completeCoefficientBoundaryExponent K n h))
          (completeCoefficientBoundarySection K n h b i)) =
      completeCoefficientBoundarySection K n h a i := by
  exact homogeneousBoundarySection_transition K n h
    (completeCoefficientCoordinates K n h).degree
    ((completeCoefficientCoordinates K n h).coordinate i)
    ((completeCoefficientCoordinates K n h).homogeneous i) f

end FLT.Mazur.PolygonInfinitesimalStages
