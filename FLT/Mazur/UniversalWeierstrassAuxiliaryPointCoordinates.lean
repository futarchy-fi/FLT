/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryRelativePoint

/-!
# Actual affine auxiliary coordinates under coefficient extension

The evaluated coordinate homomorphism retains the original affine marked
section. Its coefficient extension is the original auxiliary chart evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

/-- Evaluation of the original coordinate functions retains the actual affine section. -/
theorem auxiliaryPointSections_coordinate_spec (a : Labels 4) (ha : a ≠ 1) :
    Spec.map (CommRingCat.ofHom
      ((auxiliaryPointSections f).comp (auxiliaryCoordinateSections a ha))) =
        f ≫ auxiliaryAffineSection a ha := by
  change Spec.map ((Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv ≫
    (auxiliaryAffineSection a ha).appTop ≫ f.appTop ≫
      (Scheme.ΓSpecIso (.of R)).hom) = _
  rw [← Category.assoc (auxiliaryAffineSection a ha).appTop f.appTop,
    ← Scheme.Hom.comp_appTop, Spec.map_comp, Spec.map_comp,
    SpecMap_ΓSpecIso_hom, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The coordinate evaluation after extension retains every original coordinate function. -/
theorem auxiliaryPullbackEvaluation_coefficient
    (g : AuxiliarySectionRing →+* R) (a : Labels 4) (ha : a ≠ 1) :
    let _ : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
    (auxiliaryPullbackEvaluation g a ha).toRingHom.comp
      (chartCoefficientMap (S := R) smoothEquation 2).toRingHom =
        g.comp (auxiliaryCoordinateSections a ha) := by
  dsimp only
  let _ : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
  let k : Coordinate smoothEquation 2 →ₐ[ParameterRing] R :=
    { toRingHom := g.comp (auxiliaryCoordinateSections a ha)
      commutes' := fun r => congrArg g (auxiliaryCoordinateSections_coeff a ha r) }
  change (((auxiliaryPullbackEvaluation g a ha).restrictScalars ParameterRing).comp
    (chartCoefficientMap (S := R) smoothEquation 2)).toRingHom = k.toRingHom
  apply congrArg AlgHom.toRingHom
  apply hom_ext
  intro i
  exact (congrArg (auxiliaryPullbackEvaluation g a ha)
    (chartCoefficientMap_coord (S := R) smoothEquation 2 i)).trans
      (auxiliaryPullbackEvaluation_coord g a ha i)

/-- The pulled-back affine section projects to the original marked section. -/
@[reassoc] theorem auxiliaryPullbackSection_coefficient (a : Labels 4) (ha : a ≠ 1) :
    let _ : Algebra ParameterRing R :=
      (auxiliaryCoefficientHom (auxiliaryPointSections f)).toAlgebra
    auxiliaryPullbackSection (auxiliaryPointSections f) a ha ≫
      integralCoefficientMorphism (S := R) smoothEquation = f ≫ (auxiliaryMarking 4 a).left := by
  let _ : Algebra ParameterRing R :=
    (auxiliaryCoefficientHom (auxiliaryPointSections f)).toAlgebra
  dsimp only
  change (Spec.map (CommRingCat.ofHom
    (auxiliaryPullbackEvaluation (auxiliaryPointSections f) a ha).toRingHom) ≫
      integralCurveChart (smoothEquation.map (algebraMap ParameterRing R)) 2) ≫
        integralCoefficientMorphism (S := R) smoothEquation = _
  rw [Category.assoc, integralCurveChart_coefficientMorphism (S := R) smoothEquation 2]
  rw [← Category.assoc, chartCoefficientMorphism, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((auxiliaryPullbackEvaluation (auxiliaryPointSections f) a ha).toRingHom.comp
      (chartCoefficientMap (S := R) smoothEquation 2).toRingHom)) ≫ _ = _
  rw [auxiliaryPullbackEvaluation_coefficient, auxiliaryPointSections_coordinate_spec,
    Category.assoc, auxiliaryAffineSection_inclusion]

end FLT.Mazur.UniversalWeierstrass
