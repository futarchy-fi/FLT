/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCoordinateEvaluation
public import FLT.Mazur.SectionCubicEquationPullback

/-!
# Proved equations for the original cubic's coordinate sections

The normalized equations follow from the original quotient relations and
the injective chart section comparison. No equation is supplied as input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.WeierstrassIntegralChart
open FCurve ProjectiveSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The actual ratios satisfy the original equation on its entire inverse-image chart. -/
theorem integralCoordinateSection_chart_equation (j : Fin 3) :
    (W.map (sectionChartScalars (integralCoordinateScalars W)
      (integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j))).toProjective.Equation
        (fun i ↦ sectionRatioOn (integralCoordinateLine W) (integralCoordinateSection W j)
          (integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j)
          (integralCoordinateSection_preimage W j).le (integralCoordinateSection W i)) := by
  apply (WeierstrassCurve.Projective.map_equation _
    (ConcreteCategory.bijective_of_isIso (cubicChartSections W j)).injective _).mp
  have he := (coord_equation W j).map (Scheme.ΓSpecIso (.of (Coordinate W j))).inv.hom
  change ((W.map _).map _).toProjective.Equation _ at he ⊢
  simpa only [WeierstrassCurve.map_map, integralCoordinateScalars_chart,
    Function.comp_def, integralCoordinateSection_chart_value] using he

/-- The constructed coordinate sections satisfy all three required normalized equations. -/
theorem integralCoordinateSections_equations :
    CubicCoordinateEquations (integralCoordinateLine W) W
      (integralCoordinateSection W) (integralCoordinateScalars W) := by
  intro j
  have he := integralCoordinateSection_chart_equation W j
  generalize_proofs hU at he
  revert hU he
  rw [integralCoordinateSection_preimage]
  exact fun _ he ↦ he

/-- Every actual morphism to the original cubic supplies coordinates with proved equations. -/
theorem integralCoordinateSections_pullback_equations {X : Scheme} (f : X ⟶ integralCurve W) :
    CubicCoordinateEquations ((pullback f).obj (integralCoordinateLine W)) W
      (fun i ↦ pullGlobal f (integralCoordinateLine W) (integralCoordinateSection W i))
      (f.appTop.hom.comp (integralCoordinateScalars W)) :=
  sectionCubicEquations_pullback f (integralCoordinateLine W) W (integralCoordinateSection W)
    (integralCoordinateLine_locallyFreeRankOne W) (integralCoordinateScalars W)
    (integralCoordinateSections_equations W)

end FLT.Mazur.WeierstrassIntegralChart
