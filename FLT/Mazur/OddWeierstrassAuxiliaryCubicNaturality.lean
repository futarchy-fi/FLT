/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySourceMap
public import FLT.Mazur.UniversalWeierstrassAuxiliarySourceMap

/-!
# Cubic projections commute with arbitrary source maps

Both actual cubic projections retain the original global-sections coefficient
transition. Equality follows from the Cartesian proper coefficient comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T U : Scheme} (f : T ⟶ levelThree.left) (k : U ⟶ T)

/-- The original cubic projection commutes with every actual source morphism. -/
@[reassoc] theorem auxiliarySchemeOriginalCubicProjection_natural :
    auxiliarySchemeOriginalCubicProjection (k ≫ f) ≫
        auxiliaryOriginalCoefficientTransition f.appTop.hom k.appTop.hom =
      auxiliarySchemeOriginalSourceMap f k ≫ auxiliarySchemeOriginalCubicProjection f := by
  apply UniversalWeierstrass.properCoefficientMap_hom_ext oddChartEquation _
    (auxiliaryCoefficientHom f.appTop.hom)
    (auxiliaryPullbackEquation_coefficient f.appTop.hom)
  · change (_ ≫ _) ≫ auxiliaryOriginalCoefficientProjection f.appTop.hom =
      (_ ≫ _) ≫ auxiliaryOriginalCoefficientProjection f.appTop.hom
    have hn : auxiliaryOriginalCoefficientTransition f.appTop.hom k.appTop.hom ≫
        auxiliaryOriginalCoefficientProjection f.appTop.hom =
      auxiliaryOriginalCoefficientProjection (k ≫ f).appTop.hom :=
        auxiliaryOriginalCoefficientProjection_natural f.appTop.hom k.appTop.hom
    rw [Category.assoc, hn, auxiliarySchemeOriginalCubicProjection_coefficient]
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ auxiliarySchemeOriginalSourceMap f k ≫ z)
        (auxiliarySchemeOriginalCubicProjection_coefficient f)).trans
        (auxiliarySchemeOriginalSourceMap_fst f k))).symm
  · have ht : auxiliaryOriginalCoefficientTransition f.appTop.hom k.appTop.hom ≫
        integralCurveStructure (auxiliaryPullbackEquation f.appTop.hom) =
      integralCurveStructure (auxiliaryPullbackEquation (k ≫ f).appTop.hom) ≫ Spec.map k.appTop :=
        properCoefficientMap_structure _ _ _
          (auxiliaryPullbackEquation_natural f.appTop.hom k.appTop.hom)
    rw [Category.assoc, ht,
      auxiliarySchemeOriginalCubicProjection_structure_assoc, Category.assoc,
      auxiliarySchemeOriginalCubicProjection_structure,
      auxiliarySchemeOriginalSourceMap_snd_assoc, Scheme.toSpecΓ_naturality]

/-- The normalized cubic projection commutes with the same actual source morphism. -/
@[reassoc] theorem auxiliarySchemeNormalizedCubicProjection_natural :
    auxiliarySchemeNormalizedCubicProjection (k ≫ f) ≫
        auxiliaryNormalizedCoefficientTransition f.appTop.hom k.appTop.hom =
      auxiliarySchemeNormalizedSourceMap f k ≫ auxiliarySchemeNormalizedCubicProjection f := by
  apply UniversalWeierstrass.properCoefficientMap_hom_ext oddChartEquation _
    (auxiliaryNormalizedCoefficientHom f.appTop.hom)
    (auxiliaryNormalizedCoefficientHom_equation f.appTop.hom).symm
  · change (_ ≫ _) ≫ auxiliaryNormalizedCoefficientProjection f.appTop.hom =
      (_ ≫ _) ≫ auxiliaryNormalizedCoefficientProjection f.appTop.hom
    have hn : auxiliaryNormalizedCoefficientTransition f.appTop.hom k.appTop.hom ≫
        auxiliaryNormalizedCoefficientProjection f.appTop.hom =
      auxiliaryNormalizedCoefficientProjection (k ≫ f).appTop.hom :=
        auxiliaryNormalizedCoefficientProjection_natural f.appTop.hom k.appTop.hom
    rw [Category.assoc, hn, auxiliarySchemeNormalizedCubicProjection_coefficient]
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ auxiliarySchemeNormalizedSourceMap f k ≫ z)
        (auxiliarySchemeNormalizedCubicProjection_coefficient f)).trans
        (auxiliarySchemeNormalizedSourceMap_fst f k))).symm
  · have ht : auxiliaryNormalizedCoefficientTransition f.appTop.hom k.appTop.hom ≫
        integralCurveStructure (auxiliaryNormalizedEquation f.appTop.hom) =
      integralCurveStructure (auxiliaryNormalizedEquation (k ≫ f).appTop.hom) ≫ Spec.map k.appTop :=
        properCoefficientMap_structure _ _ _
          (auxiliaryNormalizedEquation_natural f.appTop.hom k.appTop.hom)
    rw [Category.assoc, ht,
      auxiliarySchemeNormalizedCubicProjection_structure_assoc, Category.assoc,
      auxiliarySchemeNormalizedCubicProjection_structure,
      auxiliarySchemeNormalizedSourceMap_snd_assoc, Scheme.toSpecΓ_naturality]

end FLT.Mazur.OddWeierstrassParameter
