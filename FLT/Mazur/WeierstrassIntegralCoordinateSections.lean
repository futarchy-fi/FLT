/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveCoordinateSectionRatios
public import FLT.Mazur.WeierstrassIntegralProjectiveClosed
public import FLT.Mazur.ModuleSectionProjectiveNaturality

/-!
# The original integral cubic's coordinate line and sections

Pullback of the actual hyperplane coordinates constructs three sections on
the specified cubic. Their generator opens are its original normalized charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.WeierstrassIntegralChart
open FCurve ProjectiveSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The coordinate line on the specified integral cubic, over its original ring. -/
def integralCoordinateLine : (integralCurve W).Modules :=
  (pullback (integralProjectiveMap W)).obj (O R 2 1)

/-- The original homogeneous coordinates as actual global line sections. -/
def integralCoordinateSection (i : Fin 3) : Γ(integralCoordinateLine W, ⊤) :=
  pullGlobal (integralProjectiveMap W) (O R 2 1) (coordinateGlobalSection R (Fin 3) i)

/-- The coordinate line is locally free of rank one without a smoothness assumption. -/
theorem integralCoordinateLine_locallyFreeRankOne :
    LocallyFreeRankOne (integralCoordinateLine W) :=
  (O_locallyFreeRankOne R 2 1).pullback (integralProjectiveMap W)

/-- Each constructed section generates exactly on the corresponding original cubic chart. -/
theorem integralCoordinateSection_generatorOpen (j : Fin 3) :
    sectionGeneratorOpen (integralCoordinateLine W) (integralCoordinateSection W j) =
      (integralCurveChart W j).opensRange := by
  change sectionGeneratorOpen ((pullback (integralProjectiveMap W)).obj (O R 2 1))
    (pullGlobal (integralProjectiveMap W) (O R 2 1)
      (coordinateGlobalSection R (Fin 3) j)) = _
  rw [sectionGeneratorOpen_pullGlobal (O_locallyFreeRankOne R 2 1),
    coordinateGlobalSection_generatorOpen, integralProjectiveMap_preimage_chart]

/-- The three original coordinates generate everywhere on the integral cubic. -/
theorem integralCoordinateSections_cover :
    (⨆ j, sectionGeneratorOpen (integralCoordinateLine W)
      (integralCoordinateSection W j)) = ⊤ :=
  sectionGeneratorCover_pullback (integralProjectiveMap W) (O R 2 1)
    (O_locallyFreeRankOne R 2 1) 2 (coordinateGlobalSection R (Fin 3))
    (coordinateGlobalSections_cover R (Fin 3))

/-- The integral coordinates retain the actual projective ratios on every smaller open. -/
theorem integralCoordinateSection_ratio (i j : Fin 3) (V : (integralCurve W).Opens)
    (hV : V ≤ integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j)
    (hj : V ≤ sectionGeneratorOpen (integralCoordinateLine W)
      (integralCoordinateSection W j)) :
    sectionRatioOn (integralCoordinateLine W) (integralCoordinateSection W j) V hj
        (integralCoordinateSection W i) =
      (integralProjectiveMap W).appLE (chart R (Fin 3) j) V hV
        (chartCoordinateSection R (Fin 3) j i) :=
  coordinateGlobalSection_pullback_ratio R (Fin 3) (integralProjectiveMap W) i j V hV hj

end FLT.Mazur.WeierstrassIntegralChart
