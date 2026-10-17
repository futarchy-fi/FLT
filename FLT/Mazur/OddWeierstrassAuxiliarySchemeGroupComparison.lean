/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSchemeBaseChangeComparison
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeRelativePoint

/-!
# Odd characteristic chart: actual normalization compares group families on every source scheme

Pullback along the canonical map to global sections extends the constructed
coefficient and normalization group isomorphisms to arbitrary schemes. The
result compares the actual universal families at the two actual level points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- The actual universal group family at the original auxiliary scheme point. -/
def auxiliarySchemeGroup : CommGrp (Over T) :=
  (Over.pullback (f ≫ levelThree.hom)).mapCommGrp.obj
    (integralCurveGroup oddChartEquation oddChart_discriminant)

/-- The evaluated original cubic over global sections recovers the actual source family. -/
irreducible_def auxiliarySchemeCoefficientGroupIso :
    (Over.pullback T.toSpecΓ).mapCommGrp.obj (auxiliaryPullbackGroup f.appTop.hom) ≅
      auxiliarySchemeGroup f :=
  (Over.pullback T.toSpecΓ).mapCommGrp.mapIso (auxiliaryCoefficientGroupIso f.appTop.hom) ≪≫
    (GroupSchemeBaseChange.compIso T.toSpecΓ (auxiliaryCoefficientBase f.appTop.hom)
      (integralCurveGroup oddChartEquation oddChart_discriminant)).symm ≪≫
    GroupSchemeBaseChange.congrIso (auxiliarySchemeSections_base f) _

/-- The evaluated normalized cubic recovers the actual universal normalized source family. -/
irreducible_def auxiliarySchemeNormalizedCoefficientGroupIso :
    (Over.pullback T.toSpecΓ).mapCommGrp.obj (auxiliaryNormalizedGroup f.appTop.hom) ≅
      auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f) :=
  (Over.pullback T.toSpecΓ).mapCommGrp.mapIso
      (auxiliaryNormalizedCoefficientGroupIso f.appTop.hom) ≪≫
    (GroupSchemeBaseChange.compIso T.toSpecΓ
      (auxiliaryNormalizedCoefficientBase f.appTop.hom)
      (integralCurveGroup oddChartEquation oddChart_discriminant)).symm ≪≫
    GroupSchemeBaseChange.congrIso (auxiliarySchemeNormalizedPoint_base f).symm _

/-- Normalization is a group isomorphism of the actual families over any source scheme. -/
irreducible_def auxiliarySchemeNormalizationGroupIso :
    auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f) ≅ auxiliarySchemeGroup f :=
  (auxiliarySchemeNormalizedCoefficientGroupIso f).symm ≪≫
    (Over.pullback T.toSpecΓ).mapCommGrp.mapIso (auxiliaryNormalizationGroupIso f.appTop.hom) ≪≫
    auxiliarySchemeCoefficientGroupIso f

/-- The group comparison is an isomorphism of the actual proper families over the source. -/
def auxiliarySchemeNormalizationOverIso :
    (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X ≅
      (auxiliarySchemeGroup f).X :=
  (CommGrp.forget (Over T)).mapIso (auxiliarySchemeNormalizationGroupIso f)

/-- The actual comparison retains the unchanged arbitrary source base. -/
@[reassoc] theorem auxiliarySchemeNormalizationOverIso_base :
    (auxiliarySchemeNormalizationOverIso f).hom.left ≫ (auxiliarySchemeGroup f).X.hom =
      (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.hom :=
  (auxiliarySchemeNormalizationOverIso f).hom.w

/-- The original arbitrary-source coefficient comparison retains its actual projection. -/
@[reassoc] theorem auxiliarySchemeCoefficientGroupIso_fst :
    (auxiliarySchemeCoefficientGroupIso f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (f ≫ levelThree.hom) =
        pullback.fst (auxiliaryPullbackGroup f.appTop.hom).X.hom T.toSpecΓ ≫
          (auxiliaryCoefficientGroupIso f.appTop.hom).hom.hom.hom.hom.left ≫
            pullback.fst universalGroup.hom (auxiliaryCoefficientBase f.appTop.hom) := by
  rw [auxiliarySchemeCoefficientGroupIso_def]
  exact GroupSchemeBaseChange.coefficientComparison_fst _ _ _ _ _ _ _

/-- The normalized arbitrary-source coefficient comparison retains its actual projection. -/
@[reassoc] theorem auxiliarySchemeNormalizedCoefficientGroupIso_fst :
    (auxiliarySchemeNormalizedCoefficientGroupIso f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom
        (auxiliarySchemeNormalizedPoint f ≫ levelThree.hom) =
          pullback.fst (auxiliaryNormalizedGroup f.appTop.hom).X.hom T.toSpecΓ ≫
            (auxiliaryNormalizedCoefficientGroupIso f.appTop.hom).hom.hom.hom.hom.left ≫
              pullback.fst universalGroup.hom
                (auxiliaryNormalizedCoefficientBase f.appTop.hom) := by
  rw [auxiliarySchemeNormalizedCoefficientGroupIso_def]
  exact GroupSchemeBaseChange.coefficientComparison_fst _ _ _ _ _ _ _

end FLT.Mazur.OddWeierstrassParameter
