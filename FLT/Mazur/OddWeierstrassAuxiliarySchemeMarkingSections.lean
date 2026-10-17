/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryCoefficientCharts
public import FLT.Mazur.OddWeierstrassAuxiliaryProperNormalization
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarkingComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliarySourceMap

/-!
# Actual odd auxiliary sections over arbitrary source schemes

The original source morphism is recovered from its evaluated affine sections.
Proper normalization then identifies the normalized marking with its actual
affine evaluation, including on nonaffine and nonreduced source schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- Global coordinate evaluation recovers the entire original affine section. -/
theorem auxiliarySchemeSections_coordinate_spec (a : Labels 3) (ha : a ≠ 1) :
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (f.appTop.hom.comp (auxiliaryCoordinateSections a ha))) =
        f ≫ auxiliaryAffineSection a ha := by
  change T.toSpecΓ ≫ Spec.map
    ((Scheme.ΓSpecIso (.of (Coordinate oddChartEquation 2))).inv ≫
      (auxiliaryAffineSection a ha).appTop ≫ f.appTop) = _
  rw [← Scheme.Hom.comp_appTop, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The original evaluated proper section retains its actual universal marked projection. -/
@[reassoc] theorem auxiliarySchemePullbackSection_coefficient (a : Labels 3) (ha : a ≠ 1) :
    T.toSpecΓ ≫ auxiliaryPullbackSection f.appTop.hom a ha ≫
      auxiliaryOriginalCoefficientProjection f.appTop.hom =
        f ≫ (levelThreeMarking a).left := by
  rw [auxiliaryPullbackSection, Category.assoc, ← auxiliaryOriginalChartMap_chart]
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((auxiliaryPullbackEvaluation f.appTop.hom a ha).toRingHom.comp
      (auxiliaryOriginalChartMap f.appTop.hom 2))) ≫ _ = _
  rw [auxiliaryPullbackEvaluation_coefficient, ← Category.assoc,
    auxiliarySchemeSections_coordinate_spec, Category.assoc, auxiliaryAffineSection_inclusion]

/-- The complete original marking is the evaluated original section on every source. -/
theorem auxiliarySchemeOriginalParameterMarking_section (a : Labels 3) (ha : a ≠ 1) :
    (auxiliaryOriginalParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a).left =
      T.toSpecΓ ≫ auxiliaryPullbackSection f.appTop.hom a ha := by
  apply UniversalWeierstrass.properCoefficientMap_hom_ext oddChartEquation _
    (auxiliaryCoefficientHom f.appTop.hom) (auxiliaryPullbackEquation_coefficient f.appTop.hom)
  · change _ ≫ auxiliaryOriginalCoefficientProjection _ =
      (_ ≫ _) ≫ auxiliaryOriginalCoefficientProjection _
    have h := auxiliaryOriginalParameterMarking_fst f.appTop.hom
      (auxiliarySchemeRelativePoint f) a
    rw [auxiliaryCoefficientGroupIso_proper_fst] at h
    exact h.trans
      ((auxiliarySchemePullbackSection_coefficient f a ha).symm.trans
        (Category.assoc _ _ _).symm)
  · change _ ≫ (auxiliaryPullbackGroup f.appTop.hom).X.hom = _
    rw [(auxiliaryOriginalParameterMarking f.appTop.hom
      (auxiliarySchemeRelativePoint f) a).w]
    rw [Category.assoc, auxiliaryPullbackSection_structure]
    change T.toSpecΓ = T.toSpecΓ ≫ 𝟙 _
    exact (Category.comp_id _).symm

/-- The normalized marking is the actual normalized affine evaluation on every source. -/
theorem auxiliarySchemeNormalizedParameterMarking_section (a : Labels 3) (ha : a ≠ 1) :
    (auxiliaryNormalizedParameterMarking f.appTop.hom (auxiliarySchemeRelativePoint f) a).left =
      T.toSpecΓ ≫ auxiliaryNormalizedSection f.appTop.hom a ha := by
  apply (cancel_mono (auxiliaryProperNormalization f.appTop.hom).hom).mp
  rw [Category.assoc, auxiliaryNormalizedSection_original]
  have h := congrArg Over.Hom.left
    (auxiliaryNormalizedParameterMarking_compare f.appTop.hom (auxiliarySchemeRelativePoint f) a)
  rw [Over.comp_left, auxiliaryNormalizationGroupIso_hom] at h
  exact h.trans (auxiliarySchemeOriginalParameterMarking_section f a ha)

end FLT.Mazur.OddWeierstrassParameter
