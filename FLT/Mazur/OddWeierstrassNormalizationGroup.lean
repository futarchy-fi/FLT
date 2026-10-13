/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedCoefficient
public import FLT.Mazur.OddWeierstrassSpecializationGroup
public import FLT.Mazur.WeierstrassVariableChangeGroup

/-!
# Actual group comparisons for odd auxiliary normalization

Canonical frame normalization identifies the original and normalized proper
cubic groups. Both groups retain their actual universal coefficient pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original pulled-back auxiliary cubic with its constructed group law. -/
def auxiliaryPullbackGroup : CommGrp (Over (Spec (.of R))) :=
  integralCurveGroup (auxiliaryPullbackEquation g) (auxiliaryPullbackEquation_discriminant g)

/-- The normalized cubic with its constructed group law. -/
def auxiliaryNormalizedGroup : CommGrp (Over (Spec (.of R))) :=
  integralCurveGroup (auxiliaryNormalizedEquation g) (auxiliaryNormalizedEquation_discriminant g)

/-- Canonical normalization is an actual proper group isomorphism. -/
irreducible_def auxiliaryNormalizationGroupIso :
    auxiliaryNormalizedGroup g ≅ auxiliaryPullbackGroup g :=
  integralVariableChangeGroupIso _ _ (auxiliaryFrameChange g) rfl
    (auxiliaryPullbackEquation_discriminant g) (auxiliaryNormalizedEquation_discriminant g)

/-- The original auxiliary equation retains its coefficient specialization. -/
theorem auxiliaryPullbackEquation_coefficient :
    auxiliaryPullbackEquation g = oddChartEquation.map (auxiliaryCoefficientHom g) := by
  rw [auxiliaryPullbackEquation, auxiliarySectionEquation, WeierstrassCurve.map_map]
  rfl

/-- The original coefficient morphism of an auxiliary ring-valued point. -/
def auxiliaryCoefficientBase : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (auxiliaryCoefficientHom g))

/-- The original group is the full coefficient pullback, including on nonreduced bases. -/
irreducible_def auxiliaryCoefficientGroupIso : auxiliaryPullbackGroup g ≅
    (Over.pullback (auxiliaryCoefficientBase g)).mapCommGrp.obj
      (integralCurveGroup oddChartEquation oddChart_discriminant) := by
  let _ : Algebra OddChartRing R := (auxiliaryCoefficientHom g).toAlgebra
  have he : auxiliaryPullbackEquation g = oddChartEquation.map (algebraMap OddChartRing R) :=
    auxiliaryPullbackEquation_coefficient g
  have hd : IsUnit (oddChartEquation.map (algebraMap OddChartRing R)).Δ :=
    he ▸ auxiliaryPullbackEquation_discriminant g
  exact UniversalWeierstrass.equationGroupIso he _ hd ≪≫
    integralCurveCoefficientGroupIso oddChartEquation oddChart_discriminant hd

/-- The normalized group retains its actual normalized coefficient pullback. -/
irreducible_def auxiliaryNormalizedCoefficientGroupIso : auxiliaryNormalizedGroup g ≅
    (Over.pullback (auxiliaryNormalizedCoefficientBase g)).mapCommGrp.obj
      (integralCurveGroup oddChartEquation oddChart_discriminant) :=
  specializationGroupIso (auxiliaryNormalizedEquation g) (auxiliaryCoefficient_three_isUnit g)
    (auxiliaryNormalizedEquation_discriminant g)

end FLT.Mazur.OddWeierstrassParameter
