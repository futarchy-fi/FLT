/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedPointSections

/-!
# An actual normalized auxiliary point is marked-isomorphic to its original family

The equation of the actual new point is the previously constructed normalized
equation. Equality transport followed by proper normalization gives an actual
proper isomorphism, retaining the base, zero section, and every original label.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

/-- Equation equality transport preserves the original cubic structure morphism. -/
theorem auxiliaryEquationTransport_structure {W V : WeierstrassCurve R} (h : W = V) :
    eqToHom (congrArg integralCurve h) ≫ integralCurveStructure V =
      integralCurveStructure W := by
  subst V
  exact Category.id_comp _

/-- Equation equality transport preserves the original zero section. -/
theorem auxiliaryEquationTransport_zero {W V : WeierstrassCurve R} (h : W = V) :
    integralCurveZero W ≫ eqToHom (congrArg integralCurve h) = integralCurveZero V := by
  subst V
  exact Category.comp_id _

/-- Equal named coordinates identify original affine sections under equation equality. -/
theorem auxiliaryEquationTransport_section {W V : WeierstrassCurve R} (h : W = V)
    (p : Coordinate W 2 →ₐ[R] R) (q : Coordinate V 2 →ₐ[R] R)
    (hc : ∀ i, p (coord W 2 i) = q (coord V 2 i)) :
    (Spec.map (CommRingCat.ofHom p.toRingHom) ≫ integralCurveChart W 2) ≫
      eqToHom (congrArg integralCurve h) =
        Spec.map (CommRingCat.ofHom q.toRingHom) ≫ integralCurveChart V 2 := by
  subst V
  have he : p = q := hom_ext W 2 p q hc
  rw [he]
  exact Category.comp_id _

variable (f : Spec (.of R) ⟶ levelFour.left)

/-- The actual normalized point has precisely the constructed normalized coefficient map. -/
theorem auxiliaryFamilyNormalizedPoint_coefficientHom :
    auxiliaryCoefficientHom (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) =
      auxiliaryNormalizedCoefficientHom (auxiliaryPointSections f) := by
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective
    ((auxiliaryPointSections_base (auxiliaryFamilyNormalizedPoint f)).trans
      (auxiliaryFamilyNormalizedPoint_base f)))

/-- The actual new auxiliary equation is exactly the normalized original equation. -/
theorem auxiliaryFamilyNormalizedPoint_equation :
    auxiliaryPullbackEquation (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) =
      auxiliaryNormalizedEquation (auxiliaryPointSections f) := by
  rw [auxiliaryPullbackEquation_coefficient, auxiliaryFamilyNormalizedPoint_coefficientHom,
    auxiliaryNormalizedCoefficientHom_equation]

/-- An actual proper cubic isomorphism returns the new auxiliary family to its original. -/
def auxiliaryFamilyNormalizationIso :
    integralCurve (auxiliaryPullbackEquation
      (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f))) ≅
        integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections f)) :=
  eqToIso (congrArg integralCurve (auxiliaryFamilyNormalizedPoint_equation f)) ≪≫
    auxiliaryProperNormalization (auxiliaryPointSections f)

/-- The actual family comparison is over the unchanged coefficient spectrum. -/
theorem auxiliaryFamilyNormalizationIso_base :
    (auxiliaryFamilyNormalizationIso f).hom ≫
      integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections f)) =
        integralCurveStructure (auxiliaryPullbackEquation
          (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f))) := by
  change (eqToHom (congrArg integralCurve (auxiliaryFamilyNormalizedPoint_equation f)) ≫
    (auxiliaryProperNormalization (auxiliaryPointSections f)).hom) ≫ _ = _
  rw [Category.assoc]
  have hb := integralVariableChangeTo_structure
    (auxiliaryPullbackEquation (auxiliaryPointSections f))
    (auxiliaryNormalizedEquation (auxiliaryPointSections f))
    (auxiliaryFrameChange (auxiliaryPointSections f)) rfl
  rw [show (auxiliaryProperNormalization (auxiliaryPointSections f)).hom ≫
    integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections f)) =
      integralCurveStructure (auxiliaryNormalizedEquation (auxiliaryPointSections f)) from hb]
  exact auxiliaryEquationTransport_structure (auxiliaryFamilyNormalizedPoint_equation f)

/-- The actual family comparison preserves the original zero section. -/
theorem auxiliaryFamilyNormalizationIso_zero :
    integralCurveZero (auxiliaryPullbackEquation
      (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f))) ≫
        (auxiliaryFamilyNormalizationIso f).hom =
          integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections f)) := by
  change _ ≫ eqToHom (congrArg integralCurve (auxiliaryFamilyNormalizedPoint_equation f)) ≫
    (auxiliaryProperNormalization (auxiliaryPointSections f)).hom = _
  rw [← Category.assoc,
    auxiliaryEquationTransport_zero (auxiliaryFamilyNormalizedPoint_equation f),
    auxiliaryProperNormalization_zero]

/-- The actual family comparison retains each original nonidentity marked section. -/
theorem auxiliaryFamilyNormalizationIso_mark (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryPullbackSection (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) a ha ≫
      (auxiliaryFamilyNormalizationIso f).hom =
        auxiliaryPullbackSection (auxiliaryPointSections f) a ha := by
  have hc : ∀ i, auxiliaryPullbackEvaluation
      (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) a ha
        (coord (auxiliaryPullbackEquation
          (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f))) 2 i) =
      auxiliaryNormalizedEvaluation (auxiliaryPointSections f) a ha
        (coord (auxiliaryNormalizedEquation (auxiliaryPointSections f)) 2 i) := by
    intro i
    rw [auxiliaryPullbackEvaluation_coord, auxiliaryFamilyNormalizedPoint_coordinate]
  have hs := auxiliaryEquationTransport_section (auxiliaryFamilyNormalizedPoint_equation f)
    (auxiliaryPullbackEvaluation (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) a ha)
    (auxiliaryNormalizedEvaluation (auxiliaryPointSections f) a ha) hc
  change _ ≫ eqToHom (congrArg integralCurve (auxiliaryFamilyNormalizedPoint_equation f)) ≫
    (auxiliaryProperNormalization (auxiliaryPointSections f)).hom = _
  rw [← Category.assoc, show auxiliaryPullbackSection
    (auxiliaryPointSections (auxiliaryFamilyNormalizedPoint f)) a ha ≫ eqToHom
      (congrArg integralCurve (auxiliaryFamilyNormalizedPoint_equation f)) =
        auxiliaryNormalizedSection (auxiliaryPointSections f) a ha from hs,
    auxiliaryNormalizedSection_original]

end FLT.Mazur.UniversalWeierstrass
