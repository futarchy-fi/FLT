/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassEquationCoefficientCongruence
public import FLT.Mazur.OddWeierstrassAuxiliaryNormalizationFixedGroup
public import FLT.Mazur.OddWeierstrassAuxiliaryFixedCoefficient

/-!
# Odd coefficient comparisons agree on the normalized frame

The identity normalization commutes with the original and normalized coefficient
comparisons, retaining the actual equation transports inside their sealed definitions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] integralCurveGroup integralCurveCoefficientGroupIso
variable {R : Type} [CommRing R]
variable (g : AuxiliarySectionRing →+* R) (hn : SatisfiesNormalization g)

/-- The full normalization group map commutes with the actual coefficient comparison. -/
theorem auxiliaryNormalizationGroupIso_coefficient_fixed :
    auxiliaryNormalizedCoefficientGroupIso g ≪≫
        GroupSchemeBaseChange.congrIso (auxiliaryNormalizedCoefficientBase_fixed g hn)
          (integralCurveGroup oddChartEquation oddChart_discriminant) =
      auxiliaryNormalizationGroupIso g ≪≫ auxiliaryCoefficientGroupIso g := by
  rw [auxiliaryNormalizationGroupIso_fixed g hn,
    auxiliaryNormalizedCoefficientGroupIso_def, auxiliaryCoefficientGroupIso_def]
  exact equationCoefficientComparison_congr oddChartEquation oddChart_discriminant
    _ _ _ _ _ _ (auxiliaryNormalizedCoefficientHom_equation g).symm
    (auxiliaryPullbackEquation_coefficient g)
    (normalizedSlice_equation_fixed g hn) (auxiliaryNormalizedCoefficientHom_fixed g hn)
    (auxiliaryNormalizedGroup_fixed g hn)

end FLT.Mazur.OddWeierstrassParameter
