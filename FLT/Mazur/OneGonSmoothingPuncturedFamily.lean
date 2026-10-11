/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingPuncturedParameter
public import FLT.Mazur.OneGonSmoothingUniversalComparison

/-!
# The punctured boundary family compares with both original families

The same actual cubic is the restriction of the complete boundary smoothing
and the pullback of the smooth universal cubic. Both cartesian comparisons
retain the original infinity marking, and smoothness holds on the entire
punctured base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
variable (R : Type) [CommRing R]

/-- The original complete cubic restricted to its punctured parameter ring. -/
abbrev puncturedFamily : Over (Spec (.of (PuncturedRing R))) :=
  family (puncturedParameter R)

/-- The actual map from the punctured cubic to the original complete cubic. -/
def puncturedCurveInclusion :
    (puncturedFamily R).left ⟶ (family (PowerSeries.X : PowerSeries R)).left :=
  coefficientMorphism PowerSeries.X

/-- The punctured cubic is the actual base change of the complete boundary family. -/
theorem puncturedComplete_isPullback :
    IsPullback (puncturedCurveInclusion R) (puncturedFamily R).hom
      (family (PowerSeries.X : PowerSeries R)).hom (puncturedBaseInclusion R) :=
  coefficient_isPullback PowerSeries.X

/-- The restriction includes the punctured cubic as an actual open subscheme. -/
theorem puncturedCurveInclusion_isOpenImmersion :
    IsOpenImmersion (puncturedCurveInclusion R) := by
  let _ := puncturedBaseInclusion_isOpenImmersion R
  exact MorphismProperty.of_isPullback (puncturedComplete_isPullback R).flip inferInstance

/-- The punctured infinity section retains the original complete infinity marking. -/
@[reassoc] theorem puncturedCurveInclusion_marking :
    marking (puncturedParameter R) ≫ puncturedCurveInclusion R =
      puncturedBaseInclusion R ≫ marking PowerSeries.X :=
  marking_coefficientMorphism PowerSeries.X

/-- The complete boundary family is smooth of relative dimension one on its puncture. -/
theorem puncturedFamily_smooth_dimension :
    SmoothOfRelativeDimension 1 (puncturedFamily R).hom :=
  integralCurveStructure_smooth_dimension _
    (smooth_discriminant _ (puncturedParameter_isUnit R) (puncturedFactor_isUnit R))

variable (h₂ : IsUnit (2 : R))

/-- The same punctured boundary cubic maps to the original universal smooth cubic. -/
def puncturedUniversalMorphism :
    (puncturedFamily R).left ⟶ integralCurve UniversalWeierstrass.smoothEquation :=
  smoothUniversalMorphism (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R)

/-- The two original families meet in this actual cartesian smooth-family square. -/
theorem puncturedUniversal_isPullback :
    IsPullback (puncturedUniversalMorphism R h₂) (puncturedFamily R).hom
      (integralCurveStructure UniversalWeierstrass.smoothEquation)
      (Spec.map (CommRingCat.ofHom (puncturedSmoothParameter R h₂))) :=
  smoothUniversal_isPullback _ _ _ _

/-- The overlap comparison retains infinity as the original universal origin section. -/
@[reassoc] theorem puncturedUniversalMorphism_marking :
    marking (puncturedParameter R) ≫ puncturedUniversalMorphism R h₂ =
      Spec.map (CommRingCat.ofHom (puncturedSmoothParameter R h₂)) ≫
        integralCurveZero UniversalWeierstrass.smoothEquation :=
  smoothUniversalMorphism_marking _ _ _ _

end FLT.Mazur.OneGonSmoothing
