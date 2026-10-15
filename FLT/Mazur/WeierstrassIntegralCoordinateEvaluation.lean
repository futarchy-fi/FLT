/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCoordinateSections
public import FLT.Mazur.WeierstrassCubicQuotientChart

/-!
# Evaluating the original cubic's coordinate sections

The original affine chart isomorphism reads off the universal normalized
coordinates and the original coefficient map from the constructed sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.WeierstrassIntegralChart
open FCurve ProjectiveSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The original integral coefficient map on global functions of the cubic. -/
def integralCoordinateScalars : R →+* Γ(integralCurve W, ⊤) :=
  (integralCurveStructure W).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The inverse-image chart is exactly the generator open of the constructed coordinate. -/
theorem integralCoordinateSection_preimage (j : Fin 3) :
    integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j =
      sectionGeneratorOpen (integralCoordinateLine W) (integralCoordinateSection W j) := by
  rw [integralProjectiveMap_preimage_chart, integralCoordinateSection_generatorOpen]

/-- Reading an actual section ratio on the original chart gives its original coordinate. -/
theorem integralCoordinateSection_chart_value (i j : Fin 3) :
    cubicChartSections W j
      (sectionRatioOn (integralCoordinateLine W) (integralCoordinateSection W j)
        (integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j)
        (integralCoordinateSection_preimage W j).le (integralCoordinateSection W i)) =
      (Scheme.ΓSpecIso (.of (Coordinate W j))).inv (coord W j i) := by
  rw [integralCoordinateSection_ratio W i j _ le_rfl]
  have he := ConcreteCategory.congr_hom (cubicQuotient_chart_comparison W j)
    (coordinate R (Fin 3) j i)
  change cubicChartSections W j ((integralProjectiveMap W).app _
    (chartCoordinateSection R (Fin 3) j i)) =
      (Scheme.ΓSpecIso (.of (Coordinate W j))).inv
        (projectiveChartAlgebra W j (coordinate R (Fin 3) j i)) at he
  rw [projectiveChartAlgebra_coordinate] at he
  rw [← Scheme.Hom.app_eq_appLE]
  exact he

/-- Reading the original structural scalars on a chart retains the coefficient homomorphism. -/
theorem integralCoordinateScalars_chart (j : Fin 3) :
    (cubicChartSections W j).hom.comp
      (sectionChartScalars (integralCoordinateScalars W)
        (integralProjectiveMap W ⁻¹ᵁ chart R (Fin 3) j)) =
      (Scheme.ΓSpecIso (.of (Coordinate W j))).inv.hom.comp
        (algebraMap R (Coordinate W j)) := by
  have he : (Scheme.ΓSpecIso (.of R)).inv ≫ (integralCurveStructure W).appTop ≫
      (integralCurve W).presheaf.map (homOfLE le_top).op ≫ cubicChartSections W j =
      CommRingCat.ofHom (algebraMap R (Coordinate W j)) ≫
        (Scheme.ΓSpecIso (.of (Coordinate W j))).inv := by
    rw [cubicChartSections, Scheme.Hom.map_appLE]
    change (Scheme.ΓSpecIso (.of R)).inv ≫ (integralCurveStructure W).appTop ≫
      (integralCurveChart W j).appTop = _
    rw [← Scheme.Hom.comp_appTop, integralCurveChart_structure]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  exact congrArg CommRingCat.Hom.hom he

end FLT.Mazur.WeierstrassIntegralChart
