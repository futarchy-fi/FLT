/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeRelativePoint
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedCoefficientMaps

/-!
# Original and normalized sections of arbitrary auxiliary scheme families

The original morphism is retained over the spectrum of its global functions.
Cartesian coefficient comparison identifies its full marking with the evaluated
sections pulled back along the canonical affinization morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T : Scheme} (f : T ⟶ levelFour.left)

/-- Global coordinate evaluation recovers the actual original affine section. -/
theorem auxiliarySchemeSections_coordinate_spec (a : Labels 4) (ha : a ≠ 1) :
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (f.appTop.hom.comp (auxiliaryCoordinateSections a ha))) =
        f ≫ auxiliaryAffineSection a ha := by
  change T.toSpecΓ ≫ Spec.map
    ((Scheme.ΓSpecIso (.of (Coordinate smoothEquation 2))).inv ≫
      (auxiliaryAffineSection a ha).appTop ≫ f.appTop) = _
  rw [← Scheme.Hom.comp_appTop, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Pulling the evaluated section back to the source keeps the original marking. -/
@[reassoc] theorem auxiliarySchemePullbackSection_coefficient (a : Labels 4) (ha : a ≠ 1) :
    let _ : Algebra ParameterRing Γ(T, ⊤) := (auxiliaryCoefficientHom f.appTop.hom).toAlgebra
    T.toSpecΓ ≫ auxiliaryPullbackSection f.appTop.hom a ha ≫
      integralCoefficientMorphism (S := Γ(T, ⊤)) smoothEquation =
        f ≫ (auxiliaryMarking 4 a).left := by
  let _ : Algebra ParameterRing Γ(T, ⊤) := (auxiliaryCoefficientHom f.appTop.hom).toAlgebra
  dsimp only
  change T.toSpecΓ ≫ (Spec.map (CommRingCat.ofHom
    (auxiliaryPullbackEvaluation f.appTop.hom a ha).toRingHom) ≫
      integralCurveChart (smoothEquation.map (algebraMap ParameterRing Γ(T, ⊤))) 2) ≫
        integralCoefficientMorphism (S := Γ(T, ⊤)) smoothEquation = _
  rw [Category.assoc, integralCurveChart_coefficientMorphism (S := Γ(T, ⊤))]
  rw [chartCoefficientMorphism, ← Category.assoc (Spec.map _), ← Spec.map_comp]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((auxiliaryPullbackEvaluation f.appTop.hom a ha).toRingHom.comp
      (chartCoefficientMap (S := Γ(T, ⊤)) smoothEquation 2).toRingHom)) ≫ _ = _
  rw [auxiliaryPullbackEvaluation_coefficient, ← Category.assoc,
    auxiliarySchemeSections_coordinate_spec, Category.assoc, auxiliaryAffineSection_inclusion]

/-- The full original marking is the evaluated section on every source scheme. -/
theorem auxiliarySchemeFullPullbackMarking_section (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryFullPullbackMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a).left =
      T.toSpecΓ ≫ auxiliaryPullbackSection f.appTop.hom a ha := by
  let _ : Algebra ParameterRing Γ(T, ⊤) := (auxiliaryCoefficientHom f.appTop.hom).toAlgebra
  apply (integralCoefficient_isPullback (S := Γ(T, ⊤)) smoothEquation).hom_ext
  · exact (auxiliaryFullPullbackMarking_coefficient _ _ a).trans
      ((auxiliarySchemePullbackSection_coefficient f a ha).symm.trans
        (Category.assoc _ _ _).symm)
  · exact (auxiliaryFullPullbackMarking _ (auxiliarySchemeRelativePoint f) a).w.trans
      ((Category.comp_id _).symm.trans
        ((congrArg (fun k => T.toSpecΓ ≫ k)
          (auxiliaryPullbackSection_structure f.appTop.hom a ha).symm).trans
            (Category.assoc _ _ _).symm))

/-- Proper normalization retains the original evaluated section on arbitrary sources. -/
theorem auxiliarySchemeFullNormalizedMarking_section (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryFullNormalizedMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a).left =
      T.toSpecΓ ≫ auxiliaryNormalizedSection f.appTop.hom a ha := by
  rw [auxiliaryFullNormalizedMarking_left, auxiliarySchemeFullPullbackMarking_section,
    Category.assoc, auxiliaryPullbackSection_normalize]

/-- The full normalized marking retains every affine chart evaluation. -/
theorem auxiliarySchemeFullNormalizedMarking_affine (a : Labels 4) (ha : a ≠ 1) :
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (auxiliaryNormalizedEvaluation f.appTop.hom a ha).toRingHom) ≫
        integralCurveChart (auxiliaryNormalizedEquation f.appTop.hom) 2 =
          (auxiliaryFullNormalizedMarking f.appTop.hom
            (auxiliarySchemeRelativePoint f) a).left :=
  (auxiliarySchemeFullNormalizedMarking_section f a ha).symm

end FLT.Mazur.UniversalWeierstrass
